module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1368
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MaximalCompactOneParameterLinesOfLieLines
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryLieElementsGenerateOneParamLines
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle217
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle003
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle012
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle014
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HalfLinearCocycle
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EventuallyAlgebraMapMemIntegers
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsArchEquivEq
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle293
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemHomLatticeIffIntegralMatrixSplitChart
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle142
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.IteratedLiftChains
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsRationalUnitaryDeterminantMapRationalUnitaryTo
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.CharacterValueAtT
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsPowLocKMulInf
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle049
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle118
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle081
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle060
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.StandardMaximalParabolic
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle212
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle030
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle213
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyNormFinLeOne
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle136
import Development.AbelianVarietyTheory.Definitions.Foundations.NormEulerPolySubOneLe
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle150
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle170
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector

@[expose] public section

section

noncomputable section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.CompactLine

theorem exists_line_in_kInf_skew : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (n : ℕ) (W : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n) (r s : ℕ), B.IsGood σ → W.IsSkew σ B r s →
    ∀ k ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.KInf σ W B.emb, ∃ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines σ W, γ (Multiplicative.ofAdd (1 : ℝ)) = k ∧
      ∀ t, γ t ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.KInf σ W B.emb := by
  intro F E _ _ _ _ _ σ B n W r s hb hW k hk
  choose A hA hAθ using fun w => GlobalTheory.RealLift.frameEx_holds n r s _ (W.θ w) (hW.sig w) (hW.cartan w)
  have hA1 : ∀ w, GlobalTheory.RealLift.IsFrame (Complex.I • (incM F W.J).map (piInf (B.emb w))) (A w) := fun w => by
    rw [incM_map_piInf]; exact hA w
  obtain ⟨γ, hγ, Y, hgen, hKC, hγ1⟩ := GlobalTheory.RealLift.kLine_of_lineEx GlobalTheory.RealLift.exists_line_of_upq F E σ (Fin n) r s
    B.emb (incM F W.J) Complex.I A W.θ hb.cm hA1 hAθ k hk.1 hk.2
  refine ⟨γ, hγ, hγ1, fun t => ⟨hγ.2 t, fun w => ?_⟩⟩
  obtain ⟨A', hAA⟩ := (hA w).2
  exact commute_of_gen (A w) A' hAA _ _ (Y w) (hKC w) t.toAdd (hAθ w) (hgen t.toAdd w)

end GlobalTheory.CompactLine

end
end

section

open NumberField IsDedekindDomain


theorem _root_.GlobalTheory.T.exists_oneParameter_in_unitaryArchimedeanMaxCompact : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (n : ℕ) (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n) (r s : ℕ), B.IsGood σ → X.IsHerm σ B r s →
    ∀ k ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.KInf σ X B.emb, ∃ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines σ X, γ (Multiplicative.ofAdd (1 : ℝ)) = k ∧
      ∀ t, γ t ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.KInf σ X B.emb := by
  first | exact @GlobalTheory.CompactLine.exists_line_in_kInf | exact GlobalTheory.CompactLine.exists_line_in_kInf | (intros; apply GlobalTheory.CompactLine.exists_line_in_kInf <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels


theorem _root_.GlobalTheory.T.heisenbergLine_derivative_finite_span : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n d : ℕ)
    (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (ψ : AddChar (AF F) ℂ), IsStd ψ →
    ∃ (m : ℕ) (L : Fin m → SInf F (Fin n × Fin d) →ₗ[ℂ] SInf F (Fin n × Fin d)),
      ∀ u : Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), At (evI F) u → ∃ D : SInf F (Fin n × Fin d) →ₗ[ℂ] SInf F (Fin n × Fin d),
        (∀ f f₁ : SInf F (Fin n × Fin d), ActsD (evI F) (M.heisLine ψ u) f f₁ ↔ f₁ = D f) ∧
        ∀ f, D f ∈ Submodule.span ℂ (Set.range fun i => L i f) := by
  first | exact @GlobalTheory.HeisDerivSpan.heisLine_deriv_finite_span | exact GlobalTheory.HeisDerivSpan.heisLine_deriv_finite_span | (intros; apply GlobalTheory.HeisDerivSpan.heisLine_deriv_finite_span <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.PRep GlobalTheory.AdelicU GlobalTheory.LFun

theorem _root_.GlobalTheory.T.norm_satake_le_of_unitary_spherical_GL : GlobalTheory.IndefiniteRowSideFullHecke.SatakeTrivialRangeBound.SatakeTrivialBound → ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin n) (w.adicCompletion E)) V) (B : Multiset ℂˣ), GlobalTheory.LGrp.IsIrrSmooth ρ → GlobalTheory.LGrp.IsUnitarisable ρ → HasSatGL w ρ B → ∀ b ∈ B, ‖(b : ℂ)‖ ≤ ((Ideal.absNorm w.asIdeal : ℕ) : ℝ) ^ (((n : ℝ) - 1) / 2) := by
  first | exact @GlobalTheory.LFun.SatBoundGL.norm_le_of_hasSatGL | exact GlobalTheory.LFun.SatBoundGL.norm_le_of_hasSatGL | (intros; apply GlobalTheory.LFun.SatBoundGL.norm_le_of_hasSatGL <;> assumption)
end

section

open Formalism.UG (IsUnramInv GU KU Hecke dosetInd)

theorem _root_.GlobalTheory.T.exists_zonalSphericalFunction_unramifiedUnitary : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q n : ℕ), IsUnramInv ϖ σ q → ∀ α : Fin (n / 2) → ℂˣ, ∃ w : GU σ n → ℂ, GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.IsZonal ϖ q α w := by
  first | exact @GlobalTheory.IndefiniteRowSideFullHecke.ZonalExists.exists_isZonal | exact GlobalTheory.IndefiniteRowSideFullHecke.ZonalExists.exists_isZonal | (intros; apply GlobalTheory.IndefiniteRowSideFullHecke.ZonalExists.exists_isZonal <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.thetaModels_are_coverDiscreteSeries_of_harishChandra : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix.ModelsAreCoverSeries D := by
  first | exact @GlobalTheory.CoverModel.modelsAreCoverSeries_all | exact GlobalTheory.CoverModel.modelsAreCoverSeries_all | (intros; apply GlobalTheory.CoverModel.modelsAreCoverSeries_all <;> assumption)
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PlaceGen

open GlobalTheory.AdelicU

theorem piCoprod_mem {ι G : Type} [Fintype ι] [Monoid G] {N : ι → Type} [∀ i, Monoid (N i)] (φ : ∀ i, N i →* G)
    (h : Pairwise fun i j => ∀ x y, Commute (φ i x) (φ j y)) (M : Submonoid G) (hM : ∀ i x, φ i x ∈ M)
    (x : ∀ i, N i) : MonoidHom.noncommPiCoprod φ h x ∈ M := by
  rw [MonoidHom.noncommPiCoprod_apply]
  exact Submonoid.noncommProd_mem _ _ _ _ fun i _ => hM i (x i)

section General

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (L : Submodule (𝓞 E) (Fin n → E))

omit [NumberField E] in
theorem levelOff_anti {S S' : Finset (HeightOneSpectrum (𝓞 F))} (h : S ⊆ S') :
    levelOff σ J L S' ≤ levelOff σ J L S := fun g hg => by
  rw [mem_levelOff] at hg ⊢
  refine ⟨hg.1, fun v hv => hg.2.1 v (h hv), fun v _ => ?_⟩
  by_cases hv : v ∈ S'
  · rw [hg.2.1 v hv]; exact one_mem _
  · exact hg.2.2 v hv

theorem exists_levelOff_le [Submodule.IsFullLattice E L] (U : Subgroup (GAd σ J)) (hU : IsOpen (U : Set (GAd σ J))) :
    ∃ S, levelOff σ J L S ≤ U := by
  classical
  by_contra hcon
  push Not at hcon
  obtain ⟨g, hg⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
    (fun S : Finset (HeightOneSpectrum (𝓞 F)) => (levelOff σ J L S : Set (GAd σ J)) \ (U : Set (GAd σ J)))
    (fun S S' => ⟨S ∪ S', Set.diff_subset_diff_left (levelOff_anti σ J L Finset.subset_union_left),
      Set.diff_subset_diff_left (levelOff_anti σ J L Finset.subset_union_right)⟩)
    (fun S => Set.diff_nonempty.2 (hcon S))
    (fun S => (isCompact_levelOff σ J L S).diff hU)
    (fun S => ((isCompact_levelOff σ J L S).diff hU).isClosed)
  rw [Set.mem_iInter] at hg
  have h1 : g = 1 := GAd_ext σ J
    (fun w => by rw [mem_finPts_iff_forall.1 (mem_levelOff.1 (hg ∅).1).1 w, map_one])
    fun v => by rw [(mem_levelOff.1 (hg {v}).1).2.1 v (Finset.mem_singleton_self v), map_one]
  exact (hg ∅).2 (h1 ▸ one_mem U)

omit [NumberField E] in
theorem emb_proj_mem_levelOff {S : Finset (HeightOneSpectrum (𝓞 F))} {k : GAd σ J} (hk : k ∈ levelOff σ J L S)
    (v : HeightOneSpectrum (𝓞 F)) : emb σ J v (proj σ J v k) ∈ levelOff σ J L S := by
  by_cases hv : v ∈ S
  · rw [(mem_levelOff.1 hk).2.1 v hv, map_one]; exact one_mem _
  · exact emb_mem_levelOff hv ((mem_levelOff.1 hk).2.2 v hv)

theorem eq_top_of_local [Submodule.IsFullLattice E L] (M : Submonoid (GAd σ J)) (S : Finset (HeightOneSpectrum (𝓞 F)))
    (h1 : ∀ v x, emb σ J v x ∈ M) (h2 : ∀ w x, embArch σ J w x ∈ M) (h3 : ∀ k ∈ levelOff σ J L S, k ∈ M) :
    M = ⊤ := by
  classical
  refine top_unique fun g _ => ?_
  have hinf : ∀ y, ofInf σ J y ∈ M := fun y => by
    rw [← (infEquivPi σ J).symm_apply_apply y]
    generalize infEquivPi σ J y = x
    have : embArchPi σ J x ∈ M.comap (ofInf σ J) := by
      exact piCoprod_mem (fun w => embArchInf σ J w) _ _ (fun w y => h2 w y) x
    exact this
  have hat : ∀ S' x, embAt σ J S' x ∈ M := fun S' x => by
    exact piCoprod_mem (fun v : S' => emb σ J v) _ _ (fun v y => h1 v y) x
  have hf := Filter.eventually_cofinite.1 (eventually_proj_mem_stabLoc σ J L g)
  set g' := ofFin σ J (projFin σ J g) with hg'
  set S' := S ∪ hf.toFinset with hS'
  have hfin : g' ∈ finPts σ J := mem_finPts.2 (by simp [hg'])
  have hx := mem_atPts.1 (embAt_mem σ J S' (projAt σ J S' g'))
  have hrest : (partAway σ J S' g' : GAd σ J) ∈ levelOff σ J L S' := by
    refine mem_levelOff.2 ⟨mul_mem (inv_mem hx.1) hfin, mem_awayPts.1 (partAway σ J S' g').2, fun v hv => ?_⟩
    change proj σ J v ((embAt σ J S' (projAt σ J S' g'))⁻¹ * g') ∈ _
    rw [map_mul, map_inv, hx.2 v hv, inv_one, one_mul, hg', proj_ofFin, projFinLoc_projFin]
    by_contra hc
    exact hv (Finset.mem_union_right _ (hf.mem_toFinset.2 hc))
  rw [← ofInf_projInf_mul_ofFin_projFin σ J g, ← hg', ← embAt_mul_partAway σ J S' g']
  exact mul_mem (hinf _) (mul_mem (hat _ _) (h3 _ (levelOff_anti σ J L Finset.subset_union_left hrest)))

end General

theorem gen_by_local : ∀ (D : D7) (V : HSp D) (U : Subgroup (GA D V)), IsOpen (U : Set (GA D V)) → (∀ g : GA D V, {p : Place D | ¬ (gAt V p g ∈ U ∧ gAt V p g ∈ GfC V)}.Finite) ∧ Submonoid.closure ({g : GA D V | ∃ p, gAt V p g = g} ∪ {k : GA D V | k ∈ U ∧ k ∈ GfC V ∧ ∀ p, gAt V p k ∈ U ∧ gAt V p k ∈ GfC V}) = ⊤ := by
  intro D V U hU
  haveI hL : Submodule.IsFullLattice D.host.E (stdLattice D.host.E V.rank) := isLattice_stdLattice
  obtain ⟨S, hS⟩ := exists_levelOff_le D.sp.cm.sig V.gram (stdLattice D.host.E V.rank) U hU
  have hG : ∀ k ∈ levelOff D.sp.cm.sig V.gram (stdLattice D.host.E V.rank) S, k ∈ U ∧ k ∈ GfC V :=
    fun k hk => ⟨hS hk, (mem_levelOff.1 hk).1⟩
  refine ⟨fun g => ?_, eq_top_of_local D.sp.cm.sig V.gram (stdLattice D.host.E V.rank) _ S
    (fun v x => Submonoid.subset_closure (Or.inl ⟨.inl v, by simp [gAt]⟩)) (fun w x => ?_) fun k hk => ?_⟩
  · have hf := Filter.eventually_cofinite.1
      (eventually_proj_mem_stabLoc D.sp.cm.sig V.gram (stdLattice D.host.E V.rank) g)
    haveI : Finite D.what₂.Tau := Finite.of_injective _ (placeOf_bijective D).1
    refine (((hf.union S.finite_toSet).image Sum.inl).union (Set.finite_range Sum.inr)).subset ?_
    rintro (v | τ) hp
    · refine Or.inl ⟨v, ?_, rfl⟩
      by_contra hc
      rw [Set.mem_union, not_or] at hc
      exact hp (hG _ (emb_mem_levelOff hc.2 (not_not.1 hc.1)))
    · exact Or.inr ⟨τ, rfl⟩
  · obtain ⟨τ, rfl⟩ : ∃ τ, plTau D τ = w := (placeOf_bijective D).2 w
    refine Submonoid.subset_closure (Or.inl ⟨.inr τ, ?_⟩)
    simp only [gAt, projArch_embArch_self]
  · refine Submonoid.subset_closure (Or.inr ⟨(hG k hk).1, (hG k hk).2, ?_⟩)
    rintro (v | τ)
    · exact hG _ (emb_proj_mem_levelOff _ _ _ hk v)
    · have : gAt V (.inr τ) k = 1 := by
        simp only [gAt, mem_finPts_iff_forall.1 (mem_levelOff.1 hk).1 _, map_one]
      rw [this]
      exact ⟨one_mem _, one_mem _⟩

end GlobalTheory.PlaceGen

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SplitIdealMax

theorem exists_max_of_int (D : D7) {v : FinPl D} (g : D.host.E →+* Fv D.host.F v)
    (hg : ∀ o : 𝓞 D.host.E, Valued.v (g (o : D.host.E)) ≤ 1) :
    ∃ a : D.host.E, a ∈ D.host.AA ∧ a ≠ 0 ∧ ∀ a' : D.host.E, a' ∈ D.host.AA → Valued.v (g a') ≤ Valued.v (g a) := by
  have hfg : (D.host.AA : Submodule (𝓞 D.host.E) D.host.E).FG :=
    FractionalIdeal.fg_of_isUnit _ (Ne.isUnit (GlobalTheory.SplitHomLattice.ideal_ne_zero D))
  obtain ⟨s, hs⟩ := hfg
  have hne : s.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    rintro rfl
    rw [Finset.coe_empty, Submodule.span_empty] at hs
    exact GlobalTheory.SplitHomLattice.ideal_ne_zero D (FractionalIdeal.coeToSubmodule_eq_bot.1 hs.symm)
  obtain ⟨a₀, ha₀, hmax⟩ := s.exists_max_image (fun a => Valued.v (g a)) hne
  have hle : ∀ a ∈ (D.host.AA : Submodule (𝓞 D.host.E) D.host.E), Valued.v (g a) ≤ Valued.v (g a₀) := by
    intro a ha
    rw [← hs] at ha
    induction ha using Submodule.span_induction with
    | mem a ha => exact hmax a ha
    | zero => simp only [map_zero, zero_le]
    | add x y _ _ hx hy => rw [map_add (f := _)]; exact Valuation.map_add_le _ hx hy
    | smul o x _ hx =>
      rw [show o • x = (o : D.host.E) * x from rfl, map_mul, Valuation.map_mul]
      exact (mul_le_of_le_one_left' (hg o)).trans hx
  have hmem : a₀ ∈ D.host.AA := by
    show a₀ ∈ (D.host.AA : Submodule (𝓞 D.host.E) D.host.E)
    rw [← hs]; exact Submodule.subset_span ha₀
  have h0 : a₀ ≠ 0 := by
    rintro rfl
    apply GlobalTheory.SplitHomLattice.ideal_ne_zero D
    rw [FractionalIdeal.eq_zero_iff]
    intro a ha
    have := hle a ha
    rw [map_zero, map_zero, le_zero_iff, map_eq_zero] at this
    exact (map_eq_zero g).1 this
  exact ⟨a₀, hmem, h0, fun a' ha' => hle a' ha'⟩

theorem star_int (D : D7) (o : 𝓞 D.host.E) : IsIntegral ℤ (star (o : D.host.E)) :=
  (o.2).map (starRingEnd D.host.E).toIntAlgHom

end GlobalTheory.SplitIdealMax

open GlobalTheory.SplitIdealMax in
theorem GlobalTheory.SplitIdealMax.exists_max_both : ∀ (D : D7) (v : FinPl D) (φ : SplitProj D v) (e : AE D), IsIdemOf φ e → (∃ a : D.host.E, a ∈ D.host.AA ∧ a ≠ 0 ∧ ∀ a' : D.host.E, a' ∈ D.host.AA → Valued.v (rdQ φ a') ≤ Valued.v (rdQ φ a)) ∧ (∃ a : D.host.E, a ∈ D.host.AA ∧ a ≠ 0 ∧ ∀ a' : D.host.E, a' ∈ D.host.AA → Valued.v (rdQ φ (star a')) ≤ Valued.v (rdQ φ (star a))) := by
  intro D v φ _ _
  refine ⟨exists_max_of_int D (GlobalTheory.PlaceRed.rdQh φ) fun o => GlobalTheory.PlaceRed.rdQ_int φ o,
    exists_max_of_int D ((GlobalTheory.PlaceRed.rdQh φ).comp (starRingEnd D.host.E)) fun o =>
      GlobalTheory.PlaceRed.rdQ_int φ ⟨star (o : D.host.E), star_int D o⟩⟩
end
end

section

open MeasureTheory NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Links
open GlobalTheory.IndefiniteRowSideFullHecke.IteratedLiftChains GlobalTheory.PRep GlobalTheory.LFun
open Formalism.UG (IsCommensurated Hecke)
open Formalism.MainNotions.SchurIrreducible (IsSplit)

namespace GlobalTheory.SplitValue

open WithZero GlobalTheory.CharVal GlobalTheory.Formalism.L2.Col.HostOk

theorem val_map_eq_one {E : Type} [Field E] [NumberField E] {p : ℕ} (hp : p.Prime) {w : HeightOneSpectrum (𝓞 E)}
    (hN : Ideal.absNorm w.asIdeal = p) (hsq : ((p : ℕ) : 𝓞 E) ∉ w.asIdeal ^ 2) {z : E}
    (hz : ∀ Q : HeightOneSpectrum (𝓞 E), Q ≠ w → Q.valuation E z = 1) (φ : E →+* E) (hφ : φ ≠ RingHom.id E) :
    w.valuation E (φ z) = 1 := by
  obtain ⟨Q, hQ⟩ := exists_pull φ w
  refine val_emb_eq_one hQ (hz Q fun e => hφ ?_)
  subst e
  exact GlobalTheory.ringHom_eq_of_comap_eq_unramified_degree_one E E φ (RingHom.id E) Q Q p hp hN hsq hQ (fun r => Iff.rfl)

theorem not_isOfFinOrder_val : ∀ (D : D7) (χ : Formalism.L2.Host.HChar D.host.E) (n : D.R.Psi → ℤ) (p : ℕ), (∀ v, χ.TameAt v) → χ.HasInf (Formalism.L2.Host.embPsi D.host) n → (∀ g, n g ≠ 0) → SplitsCompletely D p → ∀ w : HeightOneSpectrum (𝓞 D.host.E), (p : 𝓞 D.host.E) ∈ w.asIdeal → ¬ IsOfFinOrder (χ.val w) := by
  intro D χ n p ht hinf hn hp w hw hfin
  classical
  obtain ⟨hN, hsq⟩ := hp.2 w hw
  obtain ⟨M, z, hM, h1, h2, h3⟩ := GlobalTheory.TamePow.exists_pow_locK_mul_inf D.host.E χ
    (GlobalTheory.Mem.UnrAe.unr_ae_and_level _ χ).1.toFinset (GlobalTheory.HeckeProduct.hchar_productRule _ χ)
    (fun v hv => by simpa using hv) ht w (Formalism.L2.Host.unif w)
  obtain ⟨a, ha, hpow⟩ := isOfFinOrder_iff_pow_eq_one.1 hfin
  have h4 : χ.inf z ^ a = 1 := by
    have := congrArg (· ^ a) h3
    simp only [mul_pow, one_pow] at this
    rw [← pow_mul, mul_comm M a, pow_mul] at this
    change χ.val w ^ a = 1 at hpow
    unfold Formalism.L2.Host.HChar.val at hpow
    rwa [hpow, one_pow, one_mul] at this
  have h5 : ((χ.inf z : ℂˣ) : ℂ) ^ 2 =
      D.host.φ₀ (∏ g : D.R.Psi, (D.host.sigmaOf g z / D.host.sigmaOf g (D.host.conj z)) ^ n g) := by
    rw [hinf z, map_prod, ← Finset.prod_pow]
    refine Finset.prod_congr rfl fun g _ => ?_
    rw [map_zpow₀, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast]
    congr 1
    have e : D.host.φ₀ (D.host.sigmaOf g (D.host.conj z)) = starRingEnd ℂ (D.host.φ₀ (D.host.sigmaOf g z)) := by
      rw [sigma_conj]
      exact D.host.conjE_apply D.host.φ₀ _
    have e' : Formalism.L2.Host.embPsi D.host g z = D.host.φ₀ (D.host.sigmaOf g z) := rfl
    have h0 : D.host.φ₀ (D.host.sigmaOf g z) ≠ 0 := by simp
    rw [map_div₀, e, e', div_pow, div_eq_div_iff (pow_ne_zero _ (by simpa using h0)) (by simpa using h0), sq, mul_assoc,
      Complex.mul_conj, Complex.normSq_eq_norm_sq]
    push_cast
    rfl
  have h6 : (∏ g : D.R.Psi, (D.host.sigmaOf g z / D.host.sigmaOf g (D.host.conj z)) ^ n g) ^ a = 1 := by
    apply D.host.φ₀.injective
    rw [map_pow, ← h5, ← pow_mul, mul_comm, pow_mul, ← Units.val_pow_eq_pow_val, h4, map_one]
    simp
  have h7 := unit_of_pow (w := w) ha (by rw [h6, map_one])
  have hc : ∀ g : D.R.Psi, w.valuation _ (D.host.sigmaOf g (D.host.conj z)) = 1 := by
    intro g
    refine val_map_eq_one hp.1 hN hsq h2
      ((D.host.sigmaOf g : D.host.E →+* D.host.E).comp (D.host.conj : D.host.E →+* D.host.E)) fun e => ?_
    have := RingHom.congr_fun e D.host.sqrtMinusD
    change D.host.sigmaOf g (D.host.conj D.host.sqrtMinusD) = D.host.sqrtMinusD at this
    rw [conj_b, map_neg, sigmaOf_b] at this
    exact b_ne D.host this.symm
  have hone : D.host.sigmaOf ((1 : D.R.Psi) : D.R.GG) = 1 :=
    map_one (D.host.gal).symm
  have hg : ∀ g : D.R.Psi, g ≠ 1 → w.valuation _ (D.host.sigmaOf g z) = 1 := by
    intro g hg
    refine val_map_eq_one hp.1 hN hsq h2 (D.host.sigmaOf g : D.host.E →+* D.host.E) fun e => hg ?_
    have e1 : D.host.sigmaOf g = D.host.sigmaOf ((1 : D.R.Psi) : D.R.GG) := by
      rw [hone]
      exact AlgEquiv.ext fun x => RingHom.congr_fun e x
    exact Subtype.ext ((D.host.gal).symm.injective e1)
  rw [map_prod, Finset.prod_eq_single 1 (fun g _ h => by rw [map_zpow₀, map_div₀, hg g h, hc g, div_one, one_zpow])
    (by simp), map_zpow₀, map_div₀, hc, div_one, hone, AlgEquiv.one_apply, h1, val_unif, ← exp_nsmul, ← exp_zsmul,
    ← exp_zero, exp_inj] at h7
  simp only [nsmul_eq_mul, smul_eq_mul, mul_eq_zero] at h7
  rcases h7 with h | h | h
  · exact hn 1 h
  · omega
  · omega

end GlobalTheory.SplitValue
end

section

open scoped Matrix

theorem _root_.GlobalTheory.T.translated_standard_chain_stabilizer_radical : ∀ {K : Type} [Field K] {n m : ℕ} (Y : Fin (m + 1) → Submodule K (Fin n → K)) (d : Fin m → ℕ) (h : ∑ j, d j = n)
    (g : GL (Fin n) K), (∀ (j : Fin (m + 1)) (y : Fin n → K),
      y ∈ Y j ↔ ∀ i : Fin n, (j : ℕ) ≤ ((GlobalTheory.SmGL.blk (GlobalTheory.SmGL.stdBlocks d h) i : Fin m) : ℕ) →
        (((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ y) i = 0) →
    (∀ x : GL (Fin n) K, x ∈ GlobalTheory.IndefiniteRowSideFullHecke.StandardMaximalParabolic.conjBy g (GlobalTheory.SmGL.parab K (GlobalTheory.SmGL.stdBlocks d h)) ↔
        ∀ j, ∀ y ∈ Y j, (x : Matrix (Fin n) (Fin n) K) *ᵥ y ∈ Y j) ∧
    (∀ x : GL (Fin n) K, x ∈ GlobalTheory.IndefiniteRowSideFullHecke.StandardMaximalParabolic.conjBy g (GlobalTheory.SmGL.unipRad K (GlobalTheory.SmGL.stdBlocks d h)) ↔
        ∀ j : Fin m, ∀ y ∈ Y j.succ, (x : Matrix (Fin n) (Fin n) K) *ᵥ y - y ∈ Y j.castSucc) := by
  first | exact @GlobalTheory.StdChainStab.stdChain_stab_rad | exact GlobalTheory.StdChainStab.stdChain_stab_rad | (intros; apply GlobalTheory.StdChainStab.stdChain_stab_rad <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR GlobalTheory.WeilParts GlobalTheory.StepLaw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.isUnramifiedEtaTildeHeckeChar_of_local_components : ∀ (D : D7) (C : Formalism.L2.Host.CharFrame D) (η : (AE D)ˣ →* Circle), ChrEq η C.eta → ResEta D η 1 → IsEtaTilde D η := by
  first | exact @GlobalTheory.EtaTildeOfComponents.isEtaTilde_of_chrEq | exact GlobalTheory.EtaTildeOfComponents.isEtaTilde_of_chrEq | (intros; apply GlobalTheory.EtaTildeOfComponents.isEtaTilde_of_chrEq <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.WeilParts GlobalTheory.VecInv
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.isUnramifiedEtaTilde_of_odd_exponentSum : ∀ (D : D7) (c : (AE D)ˣ →* Circle) (χ : Formalism.L2.Host.HChar D.host.E), ChrEq c χ → Formalism.L2.Host.IsEtaT D.host χ → ∀ (μ : (AE D)ˣ →* Circle) (n m : ℕ), ResEta D μ n → ResEta D (μ * c⁻¹) m → Odd (n + m) → IsEtaTilde D c := by
  first | exact @GlobalTheory.EtaTildeOddParity.isEtaTilde_of_odd | exact GlobalTheory.EtaTildeOddParity.isEtaTilde_of_odd | (intros; apply GlobalTheory.EtaTildeOddParity.isEtaTilde_of_odd <;> assumption)
end
