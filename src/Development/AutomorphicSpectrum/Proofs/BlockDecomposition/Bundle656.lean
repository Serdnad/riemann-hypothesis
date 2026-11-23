module

public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyInterleaving.LInjective
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle002
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.IsPairLevel
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1784
import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ParabolicInductionTensorProductHasFiniteLength
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle084
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.JhMultSubAddQuot
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle382
import Development.AbelianVarietyTheory.Definitions.Foundations.GLintEqKOAndPrincEqKOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1680
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle550
import GroundTheory.AutomorphicForms.GLnLocal
import GroundTheory.LocalFields.LocalFourierHaar
public import Development.WeilBound.RepresentationTheoryGL.EisensteinResidues.AnisotropicGlobalForms.SectionTrace.SecOf
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle642
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle643
public import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.DictInf
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.BinaryMassMeans.MeanVal
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle644
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle640
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle646
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
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.Separation.Connected
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.SymIdx
import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyNormFinLeOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle622
import Development.WeilBound.ThetaLifts.Reductions.SiegelCore

@[expose] public section

section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.M

namespace GlobalTheory.CompanionTheory.WordIrr

theorem exists_lift_twKer {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {σ : Representation ℂ G V} {τ : Representation ℂ G W} (f : σ.IntertwiningMap τ)
    (hf : Function.Surjective f) {H : Subgroup G} {y : W} (hy : y ∈ twKer τ H 1) :
    ∃ x ∈ twKer σ H 1, f x = y := by
  have hint : ∀ (g : G) (u : V), f.toLinearMap (σ g u) = τ g (f.toLinearMap u) :=
    fun g u => LinearMap.congr_fun (f.isIntertwining' g) u
  have hfL : ∀ x, f x = f.toLinearMap x := fun _ => rfl
  have hy' : y ∈ Submodule.span ℂ {w | ∃ (n : H) (v : W), w = τ ↑n v - ↑((1 : H →* ℂˣ) n) • v} := hy
  clear hy
  induction hy' using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨n, v, rfl⟩ := hw
    obtain ⟨u, rfl⟩ := hf v
    refine ⟨σ ↑n u - ↑((1 : H →* ℂˣ) n) • u, Submodule.subset_span ⟨n, u, rfl⟩, ?_⟩
    simp only [hfL, map_sub, Units.smul_def, map_smul, hint]
  | zero =>
    refine ⟨0, Submodule.zero_mem _, ?_⟩
    rw [hfL]
    exact map_zero _
  | add a b _ _ ha hb =>
    obtain ⟨x1, hx1, rfl⟩ := ha
    obtain ⟨x2, hx2, rfl⟩ := hb
    refine ⟨x1 + x2, add_mem hx1 hx2, ?_⟩
    simp only [hfL, map_add (f := _)]
  | smul c a _ ha =>
    obtain ⟨x1, hx1, rfl⟩ := ha
    refine ⟨c • x1, Submodule.smul_mem _ c hx1, ?_⟩
    simp only [hfL, map_smul]

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {N s : ℕ} {d : Fin s → ℕ} {V U : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup U] [Module ℂ U]

theorem jhMult_jac_of_le (e : (Σ a, Fin (d a)) ≃ Fin N)
    {σ : Representation ℂ (Levi k fun a => Fin (d a)) U} (hσ : σ.IsIrreducible)
    {π : Representation ℂ (GL (Fin N) k) V} (hπ : IsSmooth π) {S T : Subrepresentation π} (h : T ≤ S) :
    jhMult σ (_root_.GlobalTheory.SmGL.jac e S.toRepresentation) =
      jhMult σ (_root_.GlobalTheory.SmGL.jac e T.toRepresentation) + jhMult σ (_root_.GlobalTheory.SmGL.jac e (subQuot S T)) := by
  let j : S.toRepresentation.IntertwiningMap π := ⟨S.toSubmodule.subtype, fun _ => rfl⟩
  have hS : IsSmooth S.toRepresentation := (IsSubquotient.of_injective j Subtype.val_injective).isSmooth hπ
  let ι : T.toRepresentation.IntertwiningMap S.toRepresentation := ⟨Submodule.inclusion h, fun _ => rfl⟩
  let p : S.toRepresentation.IntertwiningMap (subQuot S T) := ⟨Submodule.mkQ _, fun _ => rfl⟩
  have hp : ∀ v, p v = 0 ↔ v.1 ∈ T.toSubmodule := fun v => Submodule.Quotient.mk_eq_zero _
  have hps : Function.Surjective p := Submodule.Quotient.mk_surjective _
  refine jhMult_exact (jacMap e ι) (jacMap e p) hσ
    (GlobalTheory.JacquetExact.jacMap_injective e hS ι (Submodule.inclusion_injective h))
    (GlobalTheory.JacquetExact.jacMap_surjective e p hps) (fun u => ?_) (fun v hv => ?_)
  · obtain ⟨t, rfl⟩ := Submodule.Quotient.mk_surjective _ u
    have h0 : p (ι t) = 0 := (hp _).2 t.2
    show Submodule.Quotient.mk (p (ι t)) = 0
    rw [h0]
    rfl
  · obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ v
    have h1 : p x ∈ twKer (subQuot S T) (unipRad k e) 1 := (Submodule.Quotient.mk_eq_zero _).1 hv
    obtain ⟨y, hy, hxy⟩ := exists_lift_twKer p hps h1
    have h2 : (x - y).1 ∈ T.toSubmodule := (hp _).1 (by rw [map_sub, hxy, sub_self])
    refine ⟨Submodule.Quotient.mk ⟨(x - y).1, h2⟩, ?_⟩
    show Submodule.Quotient.mk (x - y) = Submodule.Quotient.mk x
    refine (Submodule.Quotient.eq _).2 ?_
    rw [sub_sub_cancel_left]
    exact neg_mem hy

theorem exists_irrRep_of_subrep (e : (Σ a, Fin (d a)) ≃ Fin N)
    {σ : Representation ℂ (Levi k fun a => Fin (d a)) U} (hσ : σ.IsIrreducible)
    {π : Representation ℂ (GL (Fin N) k) V} (hπ : IsSmooth π) (hl : HasFiniteLength π)
    (S : Subrepresentation π) (hS : jhMult σ (_root_.GlobalTheory.SmGL.jac e S.toRepresentation) ≠ 0) :
    ∃ τ : IrrRep (GL (Fin N) k), IsSubquotient τ.ρ S.toRepresentation ∧ jhMult σ (_root_.GlobalTheory.SmGL.jac e τ.ρ) ≠ 0 := by
  have φ := Subrepresentation.subrepresentationSubmoduleOrderIso (ρ := π)
  obtain ⟨_, _⟩ := isFiniteLength_iff_isNoetherian_isArtinian.1 hl
  have : WellFoundedGT (Subrepresentation π) := φ.toOrderEmbedding.wellFoundedGT
  have : WellFoundedLT (Subrepresentation π) := φ.toOrderEmbedding.wellFoundedLT
  induction S using WellFoundedLT.induction with
  | ind S ih =>
  rcases eq_or_ne S ⊥ with rfl | hne
  · exfalso
    apply hS
    have h0 : Subsingleton (⊥ : Subrepresentation π).toSubmodule :=
      inferInstanceAs (Subsingleton (⊥ : Submodule ℂ V))
    have h1 : Subsingleton (Jacquet (⊥ : Subrepresentation π).toRepresentation (unipRad k e)) :=
      (Submodule.Quotient.mk_surjective _).subsingleton
    exact jhMult_of_subsingleton hσ _
  obtain ⟨T, -, hT⟩ := exists_le_covBy_of_lt (bot_lt_iff_ne_bot.2 hne)
  let ι : T.toRepresentation.IntertwiningMap S.toRepresentation := ⟨Submodule.inclusion hT.le, fun _ => rfl⟩
  let p : S.toRepresentation.IntertwiningMap (subQuot S T) := ⟨Submodule.mkQ _, fun _ => rfl⟩
  let j : S.toRepresentation.IntertwiningMap π := ⟨S.toSubmodule.subtype, fun _ => rfl⟩
  rw [jhMult_jac_of_le e hσ hπ hT.le] at hS
  by_cases h0 : jhMult σ (_root_.GlobalTheory.SmGL.jac e T.toRepresentation) = 0
  · rw [h0, zero_add] at hS
    have hq : IsSubquotient (subQuot S T) S.toRepresentation :=
      .of_surjective p (Submodule.Quotient.mk_surjective _)
    have hsm : IsSmooth (subQuot S T) :=
      (hq.trans (.of_injective j Subtype.val_injective)).isSmooth hπ
    exact ⟨⟨_, subQuot S T, hsm, isIrreducible_subQuot hT⟩, hq, hS⟩
  · obtain ⟨τ, h1, h2⟩ := ih T hT.lt h0
    exact ⟨τ, h1.trans (.of_injective ι (Submodule.inclusion_injective hT.le)), h2⟩

theorem exists_irrRep_wd : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (hA : GlobalTheory.Published.IrreducibleAdmissibleGL), ∀ {N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), IsSmooth π → HasFiniteLength π → ∀ w : List (IrrGL (k := k)), Wd π w → ∃ τ : IrrRep (GL (Fin N) k), IsSubquotient τ.ρ π ∧ Wd τ.ρ w := by
  intro k _ _ _ _ hA N V _ _ π hπ hl w ⟨hd, hw⟩
  have hσ : (piTensor fun a => (w.get a).rep).IsIrreducible :=
    GlobalTheory.ProdFiniteLength.piTensor_isIrreducible_of_schur _ (fun a => (w.get a).2.rep.irr) fun a φ hφ =>
      GlobalTheory.SchurAdm.schur_admissible _ (KO k (Fin (w.get a).1)) GlobalTheory.SplitFlip.isOpen_KO
        GlobalTheory.SplitFlip.isCompact_KO _ _ (w.get a).2.rep.irr
        (hA k _ _ _ (w.get a).2.rep.smooth (w.get a).2.rep.irr) φ hφ
  have hT1 : IsSubquotient π (⊤ : Subrepresentation π).toRepresentation :=
    .of_surjective (topEquiv π).toIntertwiningMap (topEquiv π).surjective
  have hT2 : IsSubquotient (⊤ : Subrepresentation π).toRepresentation π :=
    .of_injective (topEquiv π).toIntertwiningMap (topEquiv π).injective
  have h1 : jhMult (piTensor fun a => (w.get a).rep)
      (_root_.GlobalTheory.SmGL.jac (stdBlocks (fun a => (w.get a).1) hd) (⊤ : Subrepresentation π).toRepresentation) ≠ 0 :=
    jhMult_ne_zero_iff.2 ((jhMult_ne_zero_iff.1 hw).trans
      (GlobalTheory.JacquetExact.isSubquotient_jac _ (hT2.isSmooth hπ) hT1))
  obtain ⟨τ, h2, h3⟩ := exists_irrRep_of_subrep _ hσ hπ hl ⊤ h1
  exact ⟨τ, h2.trans hT2, hd, h3⟩

end GlobalTheory.CompanionTheory.WordIrr

end
end

section

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.BCT Formalism.L2.Host PositivityTheory.Rg.BcB.F.Ex0 PositivityTheory.Rg.Bc.ArchbcB.B

namespace GlobalTheory.CompanionTheory.UnifFix

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem conj_real (x : maximalRealSubfield E) :
    IsCMField.complexConj E (algebraMap (maximalRealSubfield E) E x) = algebraMap (maximalRealSubfield E) E x := by
  exact (IsCMField.complexConj E).commutes x

theorem cj_real (w : Pl E) (x : maximalRealSubfield E) :
    GlobalTheory.BCT.cj w (algebraMap E (w.adicCompletion E) (algebraMap (maximalRealSubfield E) E x)) =
      algebraMap E (w.adicCompletion E) (algebraMap (maximalRealSubfield E) E x) := by
  unfold GlobalTheory.BCT.cj
  split_ifs with h
  · rw [h.choose_spec.2, conj_real]
  · rfl

theorem valuation_up (hU : GlobalTheory.BCT.Unr E) (w : Pl E) (x : maximalRealSubfield E) :
    w.valuation E (algebraMap (maximalRealSubfield E) E x) =
      (w.under (𝓞 (maximalRealSubfield E))).valuation (maximalRealSubfield E) x := by
  have := hU w
  have h1 := HeightOneSpectrum.valuation_liesOver E (w.under (𝓞 (maximalRealSubfield E))) w x
  have he : w.asIdeal.ramificationIdx (𝓞 (maximalRealSubfield E)) = 1 := by
    exact Ideal.ramificationIdx_eq_one_of_isUnramifiedAt
  rw [← h1, he, pow_one]

theorem neg_toAdd_unzero (a : WithZero (Multiplicative ℤ)) (h : a ≠ 0) (ha : a = WithZero.exp (-1 : ℤ)) :
    -Multiplicative.toAdd (WithZero.unzero h) = 1 := by
  subst ha
  rfl

theorem unifEx : UnifEx := by
  intro E _ _ _ hU w
  obtain ⟨π, hπ⟩ := HeightOneSpectrum.valuation_exists_uniformizer (maximalRealSubfield E)
    (w.under (𝓞 (maximalRealSubfield E)))
  have hy : w.valuation E (algebraMap (maximalRealSubfield E) E π) = WithZero.exp (-1) := by
    rw [valuation_up hU w π, hπ]
  have hy0 : algebraMap (maximalRealSubfield E) E π ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hy
    exact WithZero.zero_ne_coe hy
  have hne : algebraMap E (w.adicCompletion E) (algebraMap (maximalRealSubfield E) E π) ≠ 0 :=
    (map_ne_zero _).2 hy0
  have hv : Valued.v (algebraMap E (w.adicCompletion E) (algebraMap (maximalRealSubfield E) E π)) =
      WithZero.exp (-1) := by
    rw [HeightOneSpectrum.algebraMap_adicCompletion (𝓞 E) E w, Function.comp_apply, Algebra.algebraMap_self,
      RingHom.id_apply, HeightOneSpectrum.valuedAdicCompletion_eq_valuation', hy]
  have hv0 : Valued.v (algebraMap E (w.adicCompletion E) (algebraMap (maximalRealSubfield E) E π)) ≠ 0 := by
    rw [hv]
    exact WithZero.coe_ne_zero
  refine ⟨Units.mk0 _ hne, ⟨?_, ?_⟩, ?_⟩
  · show Formalism.UG.ordL (algebraMap E (w.adicCompletion E) (algebraMap (maximalRealSubfield E) E π)) = 1
    unfold Formalism.UG.ordL
    rw [dite_eq_right hv0]
    exact neg_toAdd_unzero _ hv0 hv
  · exact cj_real w π
  · exact hv

end GlobalTheory.CompanionTheory.UnifFix
end
end

section

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcB.F.Ex0 PositivityTheory.Rg.Bc.ArchbcB.B
open scoped Classical

namespace GlobalTheory.CompanionTheory.SecThrough

theorem secEx : SecEx := by
  intro E _ _ _ S₀ hS₀
  let f : Pl E → HeightOneSpectrum (𝓞 (maximalRealSubfield E)) := fun w => w.under (𝓞 (maximalRealSubfield E))
  have hex : ∀ y : Set.range f, ∃ u : Pl E, f u = y.1 ∧ ∀ w ∈ S₀, f w = y.1 → u = w := by
    rintro ⟨_, w₀, rfl⟩
    by_cases h : ∃ w ∈ S₀, f w = f w₀
    · obtain ⟨w, hw, hfw⟩ := h
      exact ⟨w, hfw, fun w' hw' _ => Finset.card_le_one.1 hS₀ w hw w' hw'⟩
    · exact ⟨w₀, rfl, fun w hw hfw => absurd ⟨w, hw, hfw⟩ h⟩
  let g : Set.range f → Pl E := fun y => (hex y).choose
  have hg : ∀ y, f (g y) = y.1 := fun y => (hex y).choose_spec.1
  have hg₀ : ∀ y, ∀ w ∈ S₀, f w = y.1 → g y = w := fun y => (hex y).choose_spec.2
  refine ⟨Set.range g, fun w => ⟨g ⟨f w, w, rfl⟩, ⟨⟨_, rfl⟩, hg _⟩, ?_⟩, ?_, ?_⟩
  · rintro _ ⟨⟨y, rfl⟩, hy⟩
    exact congrArg g (Subtype.ext ((hg y).symm.trans hy))
  · intro w hw
    exact ⟨⟨f w, w, rfl⟩, hg₀ _ w hw rfl⟩
  · intro w hw
    refine ⟨⟨f w, w, rfl⟩, ?_⟩
    by_contra hne
    exact hw ⟨_, hne, hg _⟩

end GlobalTheory.CompanionTheory.SecThrough

end
end

section

open NumberField IsDedekindDomain Matrix Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcB.F.Ex0 PositivityTheory.Rg.Bc.ArchbcB.B
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.CompanionTheory.SplitLevel

theorem exists_reps {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (K K' : Subgroup G)
    (hc : IsCompact (K : Set G)) (ho : IsOpen (K' : Set G)) :
    ∃ X : Finset G, (∀ x ∈ X, x ∈ K) ∧ ∀ k ∈ K, ∃! x ∈ X, x⁻¹ * k ∈ K' := by
  haveI : CompactSpace K := isCompact_iff_compactSpace.1 hc
  have hop : IsOpen ((K'.subgroupOf K : Subgroup K) : Set K) := by
    rw [Subgroup.coe_subgroupOf]
    exact ho.preimage continuous_subtype_val
  haveI : Finite (K ⧸ K'.subgroupOf K) := Subgroup.quotient_finite_of_isOpen _ hop
  haveI := Fintype.ofFinite (K ⧸ K'.subgroupOf K)
  refine ⟨Finset.univ.image fun q : K ⧸ K'.subgroupOf K => ((q.out : K) : G), ?_, ?_⟩
  · intro x hx
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hx
    exact q.out.2
  · intro k hk
    let q₀ : K ⧸ K'.subgroupOf K := QuotientGroup.mk ⟨k, hk⟩
    refine ⟨((q₀.out : K) : G), ⟨Finset.mem_image_of_mem _ (Finset.mem_univ _), ?_⟩, ?_⟩
    · have h : (q₀.out)⁻¹ * ⟨k, hk⟩ ∈ K'.subgroupOf K := QuotientGroup.eq.1 (QuotientGroup.out_eq' q₀)
      exact Subgroup.mem_subgroupOf.1 h
    · rintro x ⟨hx, hxk⟩
      obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hx
      have h : q = q₀ := by
        rw [← QuotientGroup.out_eq' q]
        exact QuotientGroup.eq.2 (Subgroup.mem_subgroupOf.2 hxk)
      rw [h]

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem congSub_conj (w : Pl E) (n m : ℕ) : ∀ k ∈ GlobalTheory.LFun.KGL w (n := n), ∀ k' ∈ GlobalTheory.PrincCong.congSub w n m,
    k * k' * k⁻¹ ∈ GlobalTheory.PrincCong.congSub w n m := by
  rintro _ ⟨h, rfl⟩ _ ⟨h', hh', rfl⟩
  refine ⟨h * h' * h⁻¹, ?_, by simp⟩
  exact Subgroup.Normal.conj_mem h' hh' h

def lev (w : Pl E) (μ : (w.adicCompletion E)ˣ →* ℂˣ) (m b : ℕ) : Subgroup (GLw b w) :=
  GlobalTheory.PrincCong.congSub w b m ⊓ μ.ker.comap GeneralLinearGroup.det

theorem continuous_det (w : Pl E) (b : ℕ) :
    Continuous (GeneralLinearGroup.det : GLw b w → (w.adicCompletion E)ˣ) :=
  Units.continuous_iff.2 ⟨Continuous.matrix_det Units.continuous_val,
    Continuous.matrix_det (Units.continuous_val.comp continuous_inv)⟩

theorem isLevel_lev (w : Pl E) (hw : IsSplitAt w) (μ : (w.adicCompletion E)ˣ →* ℂˣ)
    (hμ : IsOpen (μ.ker : Set (w.adicCompletion E)ˣ)) (m b : ℕ) :
    GlobalTheory.BCT.IsLevel (thL b w) (GlobalTheory.LFun.KGL w (n := b)) (lev w μ m b) := by
  refine ⟨?_, fun g hg => ((GlobalTheory.PrincCong.mem_congSub_iff w b m g).1 hg.1).1, fun k hk => ?_⟩
  · exact (GlobalTheory.PrincCong.isOpen_congSub w b m).inter (hμ.preimage (continuous_det w b))
  · have ht : thL b w = MonoidHom.id _ := by unfold thL; rw [if_pos hw]
    rw [ht]
    exact hk

theorem blk_mem {a b n : ℕ} (h : a + b = n) (w : Pl E) (m : ℕ) (y : GLw a w × GLw b w)
    (h1 : y.1 ∈ GlobalTheory.PrincCong.congSub w a m) (h2 : y.2 ∈ GlobalTheory.PrincCong.congSub w b m) :
    blk h w y 0 ∈ GlobalTheory.PrincCong.congSub w n m := by
  rw [GlobalTheory.CompanionTheory.GL3BlockMatrixLocal.blk_zero_eq, GlobalTheory.PrincCong.mem_congSub_iff]
  obtain ⟨k1, e1⟩ := (GlobalTheory.PrincCong.mem_congSub_iff w a m _).1 h1
  obtain ⟨k2, e2⟩ := (GlobalTheory.PrincCong.mem_congSub_iff w b m _).1 h2
  have hI1 := GlobalTheory.AdelicU.mem_GLint_iff.1 k1
  have hI2 := GlobalTheory.AdelicU.mem_GLint_iff.1 k2
  refine ⟨GlobalTheory.AdelicU.mem_GLint_iff.2 ⟨fun i j => ?_, fun i j => ?_⟩, fun i j => ?_⟩
  · rw [CtLevel.dgM_val]
    exact CtLevel.blockDiagonalMatrixOfAddEq_entries_mem_subring _ h _ _ hI1.1 hI2.1 i j
  · rw [← map_inv, CtLevel.dgM_val]
    exact CtLevel.blockDiagonalMatrixOfAddEq_entries_mem_subring _ h _ _ hI1.2 hI2.2 i j
  · obtain ⟨i', rfl⟩ := (CtLevel.blkEq h).surjective i
    obtain ⟨j', rfl⟩ := (CtLevel.blkEq h).surjective j
    have hone : ∀ p q, (1 : Matrix (Fin n) (Fin n) (w.adicCompletion E)) (CtLevel.blkEq h p) (CtLevel.blkEq h q) =
        (1 : Matrix (Fin a ⊕ Fin b) (Fin a ⊕ Fin b) (w.adicCompletion E)) p q := by
      intro p q
      simp [Matrix.one_apply, (CtLevel.blkEq h).injective.eq_iff]
    rw [hone]
    rcases i' with i' | i' <;> rcases j' with j' | j'
    · rw [(GlobalTheory.CompanionTheory.GL3BlockMatrixLocal.dgM_entries h w y).1]
      simpa [Matrix.one_apply] using e1 i' j'
    · rw [CtLevel.dgM_val, CtLevel.dgMat, reindex_apply, submatrix_apply, Equiv.symm_apply_apply,
        Equiv.symm_apply_apply]
      simp
    · rw [CtLevel.dgM_val, CtLevel.dgMat, reindex_apply, submatrix_apply, Equiv.symm_apply_apply,
        Equiv.symm_apply_apply]
      simp
    · rw [(GlobalTheory.CompanionTheory.GL3BlockMatrixLocal.dgM_entries h w y).2]
      simpa [Matrix.one_apply] using e2 i' j'

theorem splitEx : SplitEx := by
  intro E _ _ _ n w hw μ hμ m hm KB hKB
  have hKc := (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL (E := E) w n).2
  have ho := GlobalTheory.PrincCong.isOpen_congSub w n m
  have hle : GlobalTheory.PrincCong.congSub w n m ≤ GlobalTheory.LFun.KGL w (n := n) :=
    fun g hg => ((GlobalTheory.PrincCong.mem_congSub_iff w n m g).1 hg).1
  have hcl : IsClosed (GlobalTheory.PrincCong.congSub w n m : Set (GLw n w)) := Subgroup.isClosed_of_isOpen _ ho
  have hc : IsCompact (GlobalTheory.PrincCong.congSub w n m : Set (GLw n w)) := hKc.of_isClosed_subset hcl hle
  obtain ⟨X, hX, hXu⟩ := exists_reps (GlobalTheory.LFun.KGL w (n := n)) (GlobalTheory.PrincCong.congSub w n m) hKc ho
  refine ⟨GlobalTheory.PrincCong.congSub w n m, X, (GlobalTheory.PrincCong.congSub w n m : Set (GLw n w)).indicator 1,
    fun a => (lev w μ m a).prod (lev w μ m (n - a)), ?_, ho, hle, congSub_conj w n m, hX, hXu, ?_, ?_⟩
  · ext k
    rw [Subgroup.mem_subgroupOf, GlobalTheory.PrincCong.mem_congSub_iff, hKB k]
    exact Iff.rfl
  · refine ⟨ho, hc, ?_, fun k₁ hk₁ k₂ hk₂ g => ?_⟩
    · refine HasCompactSupport.of_support_subset_isCompact hc ?_
      intro g hg
      by_contra h
      exact hg (Set.indicator_of_notMem h _)
    · have hiff : k₁ * g * k₂ ∈ GlobalTheory.PrincCong.congSub w n m ↔ g ∈ GlobalTheory.PrincCong.congSub w n m := by
        rw [Subgroup.mul_mem_cancel_right _ hk₂, Subgroup.mul_mem_cancel_left _ hk₁]
      by_cases hg : g ∈ GlobalTheory.PrincCong.congSub w n m
      · rw [Set.indicator_of_mem (show _ ∈ (GlobalTheory.PrincCong.congSub w n m : Set (GLw n w)) from hiff.2 hg),
          Set.indicator_of_mem (show _ ∈ (GlobalTheory.PrincCong.congSub w n m : Set (GLw n w)) from hg)]
        rfl
      · rw [Set.indicator_of_notMem (show _ ∉ (GlobalTheory.PrincCong.congSub w n m : Set (GLw n w)) from fun h => hg (hiff.1 h)),
          Set.indicator_of_notMem (show _ ∉ (GlobalTheory.PrincCong.congSub w n m : Set (GLw n w)) from hg)]
  · intro a ha
    refine ⟨⟨_, _, rfl, isLevel_lev w hw μ hμ m a, isLevel_lev w hw μ hμ m (n - a)⟩, fun y hy => ⟨?_, ?_⟩⟩
    · exact blk_mem (Nat.add_sub_of_le ha) w m y hy.1.1 hy.2.1
    · have d1 : μ (GeneralLinearGroup.det y.1) = 1 := hy.1.2
      have d2 : μ (GeneralLinearGroup.det y.2) = 1 := hy.2.2
      rw [map_mul, map_pow, map_pow, d1, d2, one_pow, one_pow, one_mul]

end GlobalTheory.CompanionTheory.SplitLevel

end
end

section

open ResidueKilled.Tr

theorem _root_.GlobalTheory.T.divisibility_statement : Div := by
  first | exact @GlobalTheory.CompanionTheory.DivMult.div_multiplier | exact GlobalTheory.CompanionTheory.DivMult.div_multiplier | (intros; apply GlobalTheory.CompanionTheory.DivMult.div_multiplier <;> assumption)
end

section

open ResidueKilled.Tr

theorem _root_.GlobalTheory.T.scalar_section_exists : TScal := by
  first | exact @GlobalTheory.CompanionTheory.ScalWall.tScal | exact GlobalTheory.CompanionTheory.ScalWall.tScal | (intros; apply GlobalTheory.CompanionTheory.ScalWall.tScal <;> assumption)
end

section


theorem _root_.GlobalTheory.T.constant_multiplier_good : PositivityTheory.RgEis.StdGood → PositivityTheory.RgEis.Dict → PositivityTheory.RgEis.DictInf → PositivityTheory.RgEis.CMGood := by
  first | exact @GlobalTheory.CompanionTheory.RgEisCM.cmGood | exact GlobalTheory.CompanionTheory.RgEisCM.cmGood | (intros; apply GlobalTheory.CompanionTheory.RgEisCM.cmGood <;> assumption)
end

section

open PositivityTheory.Rg.Mass

theorem _root_.GlobalTheory.T.hasse_principle : Hasse := by
  first | exact @GlobalTheory.CompanionTheory.SW.MassHasse.hasse | exact GlobalTheory.CompanionTheory.SW.MassHasse.hasse | (intros; apply GlobalTheory.CompanionTheory.SW.MassHasse.hasse <;> assumption)
end

section

open PositivityTheory.Rg.Mass
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter
open scoped TensorProduct ENNReal NNReal

theorem _root_.GlobalTheory.T.archimedean_binary_gram_integral : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
  ∀ (J : Matrix (Fin 2) (Fin 2) E), IsHermND σ J → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (li : Measure (Ainf F)), IsStdInf li →
  ∀ (mi : HermR (Ainf F) σ 1 → Measure (Fin 1 → Fin 2 → Ainf F ⊗[F] E)),
  IsGramFib (Ainf F) σ J 1 (coordW (Ainf F) b li 1 2) (coordHerm (Ainf F) σ b li 1) mi →
  ∀ θ : ℝ →+* Ainf F, Continuous θ → ∀ ε : ℝ, 0 < ε → ∀ (s : Ainf F) (φ : (Fin 1 → Fin 2 → Ainf F ⊗[F] E) → ℝ), Continuous φ →
  ENNReal.ofReal (ε ^ (4 * Module.finrank ℚ F)) * ∫⁻ X, ENNReal.ofReal (φ (PositivityTheory.Rg.Mass.dil θ ε X)) ∂(mi (hermScal (Ainf F) σ s)) =
    ENNReal.ofReal ((ε ^ 2) ^ Module.finrank ℚ F) * ∫⁻ X, ENNReal.ofReal (φ X) ∂(mi (hermScal (Ainf F) σ (θ (ε ^ 2) * s))) := by
  first | exact @GlobalTheory.CompanionTheory.BinaryDil.dilation_inf_binary | exact GlobalTheory.CompanionTheory.BinaryDil.dilation_inf_binary | (intros; apply GlobalTheory.CompanionTheory.BinaryDil.dilation_inf_binary <;> assumption)
end

section

open NumberField IsDedekindDomain Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.KFin
open Formalism.UG (cT)
open scoped TensorProduct NNReal

theorem _root_.GlobalTheory.T.tensor_fixed_by_involution_is_base : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}, IsCMExt F E σ → ∀ (K : Type) [Field K] [Algebra F K] (a : K ⊗[F] E), sigR K σ a = a → ∃ x : K, algebraMap K (K ⊗[F] E) x = a := by
  first | exact @GlobalTheory.CompanionTheory.KFin.sigR_fixed_eq_algebraMap | exact GlobalTheory.CompanionTheory.KFin.sigR_fixed_eq_algebraMap | (intros; apply GlobalTheory.CompanionTheory.KFin.sigR_fixed_eq_algebraMap <;> assumption)
end
