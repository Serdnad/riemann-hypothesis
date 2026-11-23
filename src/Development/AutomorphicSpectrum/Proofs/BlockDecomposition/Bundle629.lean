module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle608
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle619
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.LeftZeroDuality.H1StructureDimLe
public import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle024
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle030
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftLeftFst
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle104
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle094
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle107
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.QuotientVanishing.Bundle001
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
import Development.AbelianVarietyTheory.Definitions.Foundations.MeasurePreservingRmulQuotMeas
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteTwConjOfIsTest
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle621
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LintegralKernelNeTop
public import Development.WeilBound.ThetaLifts.Reductions.SiegelCore
public import Formalism.UnipotentAdelicQuotients.SWXSDefs
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ExistsTraceFormGramMatrixInBasis
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle082
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle007
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ExistsSelfDualForm
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.AdeleLC
import GroundTheory.AutomorphicForms.Bundle012
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
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle459
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle430
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.Bundle001

@[expose] public section

section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WhitFree
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.fubini_fourier_hermitian_integral : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (hJ : IsHermND σ J) (n : ℕ) (hCM : IsCMExt F E σ), ∀ ψ : AddChar (AF F) ℂ, IsCharAF F ψ → ∀ (dx : Measure (Fin n → Fin M → AF F ⊗[F] E)) (db : Measure (HermR (AF F) σ n)), SFinite dx → SFinite db → ∀ Φ : (Fin n → Fin M → AF F ⊗[F] E) → ℂ, Integrable Φ dx → ∀ τ : HermR (AF F) σ n → ℂ, Integrable (GlobalTheory.CompanionTheory.SiegelND.Coef.fouH σ ψ db τ) db → (∀ z, ∫ y, GlobalTheory.CompanionTheory.SiegelND.Coef.fouH σ ψ db τ y * ψ (pairHerm (AF F) σ n y z) ∂db = τ (-z)) → ∀ (T : Matrix (Fin n) (Fin n) E) (hT : ∀ a c, σ (T c a) = T a c), Continuous (GlobalTheory.CompanionTheory.SiegelND.Coef.chiT σ ψ T) ∧ ∫ y, GlobalTheory.CompanionTheory.SiegelND.Coef.fouH σ ψ db τ y * (GlobalTheory.CompanionTheory.SiegelND.starN σ J ψ dx Φ y * GlobalTheory.CompanionTheory.SiegelND.Coef.chiT σ ψ T y) ∂db = ∫ x, Φ x * τ (hermOf (AF F) σ T hT - GlobalTheory.CompanionTheory.SiegelND.Coef.gramH hCM hJ (AF F) x) ∂dx := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.Coef.fubini_starN_fouH | exact GlobalTheory.CompanionTheory.SiegelND.Coef.fubini_starN_fouH | (intros; apply GlobalTheory.CompanionTheory.SiegelND.Coef.fubini_starN_fouH <;> assumption)
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual PositivityTheory.ObstructionTrivialLocus

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.KLFinite

theorem memKL_of_triv_lam {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} (hL : L.IsLB) {T : Over S}
    (x : T ⟶ A) (hx : Triv (ev (abelian₂ A L) (fst T A ≫ x) (snd T A))) : GlobalTheory.MemKL A L x := by
  have hP : (abelian₂ A L).IsLB := LB.isLB_linComb hL _ _
  have hl : lam (cls L hL) (fst T A ≫ x) (snd T A) = 0 := by
    have e := (triv_ev_iff hP _ _).1 hx
    rwa [evc, show cls _ hP = lam (cls L hL) (fst A A) (snd A A) from cls_cube_two hL _ _ hP, pull_lam, lift_fst,
      lift_snd] at e
  have hD : (Out.translDiff A L x).IsLB := LB.isLB_linComb hL _ _
  intro p
  obtain ⟨V, hV, hc⟩ := exists_pull_eq_zero
    (CechPic.pull x.left (cls L hL) - CechPic.pull (1 : T ⟶ A).left (cls L hL)) p
  refine ⟨V, hV, (cls_eq_zero_iff (pull_isLB hD _)).1 ?_⟩
  have e₁ := pull_translDiff hL x hD (fst T A) (snd T A)
  rw [lift_fst_snd, Over.id_left, pull_id] at e₁
  have e₂ : cls _ hD = CechPic.pull (fst T A).left
      (CechPic.pull x.left (cls L hL) - CechPic.pull (1 : T ⟶ A).left (cls L hL)) := by
    rw [e₁, map_sub, ← pull_comp, ← pull_comp, ← Over.comp_left, ← Over.comp_left, MonObj.comp_one,
      ← sub_eq_zero, ← hl, lam]
    abel
  rw [cls_pull hD, e₂, ← pull_comp]
  exact pull_eq_zero_of_mem V (((fst T A).left ⁻¹ᵁ V).ι ≫ (fst T A).left) (fun z ↦ z.2) hc

theorem memKL_congr {S X : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} {t t' : X ⟶ S} (e : t = t')
    (x : Over.mk t ⟶ A) (x' : Over.mk t' ⟶ A) (hl : x.left = x'.left) (h : GlobalTheory.MemKL A L x) :
    GlobalTheory.MemKL A L x' := by
  subst e
  have e : x = x' := Over.OverMorphism.ext hl
  rwa [← e]

theorem finite_memKL (k : Type) [Field k] [IsAlgClosed k] (B : Over (Sp k)) [GrpObj B] (hB : IsAbelianScheme B)
    (M : LB B.left) (hM : M.IsLB) (hA : Out.RelAmple B M) :
    Finite {x : 𝟙_ (Over (Sp k)) ⟶ B // GlobalTheory.MemKL B M x} := by
  obtain ⟨H, j, -, hfin, hH⟩ :=
    GlobalTheory.KernelRep.exists_finite_closed_kernel GlobalTheory.abelianSchemeLaws_all.1.globalFns k B hB M hM hA
  have : IsFinite H.hom := hfin
  have : IsFinite (toUnit H).left := hfin
  have hf := GlobalTheory.TorsionDivisible.finite_fibre_points (toUnit H) (𝟙 _)
  refine Finite.of_surjective
    (fun z : {x : 𝟙_ (Over (Sp k)) ⟶ H // x ≫ toUnit H = 𝟙 _} ↦
      (⟨z.1 ≫ j, (hH _ _).2 ⟨z.1, rfl⟩⟩ : {x : 𝟙_ (Over (Sp k)) ⟶ B // GlobalTheory.MemKL B M x})) fun x ↦ ?_
  obtain ⟨z, hz⟩ := (hH _ _).1 x.2
  exact ⟨⟨z, toUnit_unique _ _⟩, Subtype.ext hz⟩

theorem kFinite : KFinite := by
  intro S A _ hA L hL hamp k _ _ t
  let B : Over (Sp k) := (Over.pullback t).obj A
  have gp : IsGrpPullback B A t (pullback.fst A.hom t) := isGrpPullback_pullback A t
  have hB : IsAbelianScheme B := by
    have := hA.comm
    have hc : IsCommMonObj B := by
      rw [isCommMonObj_iff_isMulCommutative]
      intro T
      refine ⟨⟨fun x y => Over.OverMorphism.ext (gp.1.hom_ext ?_ (by rw [Over.w, Over.w]))⟩⟩
      rw [← gp.2 T x y (pushPt gp.1.w x) (pushPt gp.1.w y) rfl rfl,
        ← gp.2 T y x (pushPt gp.1.w y) (pushPt gp.1.w x) rfl rfl, _root_.mul_comm]
    exact ⟨hc, MorphismProperty.of_isPullback (P := @Smooth) gp.1 hA.smooth,
      MorphismProperty.of_isPullback (P := @IsProper) gp.1 hA.proper,
      MorphismProperty.of_isPullback (P := @GeometricallyConnected) gp.1 hA.geomConnected⟩
  have := hA.proper
  have hM : (L.pull (pullback.fst A.hom t)).IsLB := pull_isLB hL _
  have hAmp : Out.RelAmple B (L.pull (pullback.fst A.hom t)) :=
    GlobalTheory.AmpleBaseChange.relAmple_of_isPullback hL hamp (IsPullback.of_hasPullback A.hom t)
  have hK := finite_memKL k B hB _ hM hAmp
  have hw : ∀ x : Over.mk t ⟶ A, x.left ≫ A.hom = 𝟙 (Sp k) ≫ t := fun x ↦ by
    rw [Over.w x, Category.id_comp]; rfl
  let pt : (Over.mk t ⟶ A) → (𝟙_ (Over (Sp k)) ⟶ B) := fun x ↦ GlobalTheory.AbDual.liftPt gp (𝟙 _) x.left (hw x)
  have hpt : ∀ x, (pt x).left ≫ pullback.fst A.hom t = x.left := fun x ↦
    GlobalTheory.AbDual.liftPt_left gp _ _ _
  have hmem : ∀ x : Over.mk t ⟶ A, Triv (ev (abelian₂ A L) (fst (Over.mk t) A ≫ x) (snd (Over.mk t) A)) →
      GlobalTheory.MemKL B (L.pull (pullback.fst A.hom t)) (pt x) := fun x hx ↦
    GlobalTheory.memKL_of_push gp hL hM ((cls_eq_iff hM hM).1 rfl) (pt x)
      (memKL_congr (Category.id_comp t).symm x _ (hpt x).symm (memKL_of_triv_lam hL x hx))
  have : Finite {x : Over.mk t ⟶ A | Triv (ev (abelian₂ A L) (fst (Over.mk t) A ≫ x) (snd (Over.mk t) A))} :=
    Finite.of_injective
      (fun x ↦ (⟨pt x.1, hmem x.1 x.2⟩ : {y : 𝟙_ (Over (Sp k)) ⟶ B //
        GlobalTheory.MemKL B (L.pull (pullback.fst A.hom t)) y})) fun x y e ↦ by
      refine Subtype.ext (Over.OverMorphism.ext ?_)
      have e' : pt x.1 = pt y.1 := congrArg Subtype.val e
      rw [← hpt x.1, ← hpt y.1, e']
  exact Set.toFinite _

end GlobalTheory.CompanionTheory.KLFinite
end
end

section

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Function
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Tf.Loc PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D4
open scoped Pointwise

namespace GlobalTheory.CompanionTheory.TwUnfold

theorem mk_eq_iff_twConjugate {R : Type*} [Group R] (θ : Monoid.End R) (c : Quot (TwConjugate θ)) (d : R) :
    Quot.mk _ d = c ↔ TwConjugate θ (Quot.out c) d := by
  have hr : ∀ x, TwConjugate θ x x := fun x => ⟨1, by simp [twConj]⟩
  have hs : ∀ {x y}, TwConjugate θ x y → TwConjugate θ y x := by
    rintro x y ⟨g, rfl⟩
    refine ⟨g⁻¹, ?_⟩
    simp only [twConj, map_inv, inv_inv]
    group
  have ht : ∀ {x y z}, TwConjugate θ x y → TwConjugate θ y z → TwConjugate θ x z := by
    rintro x y z ⟨g, rfl⟩ ⟨h, rfl⟩
    refine ⟨g * h, ?_⟩
    simp only [twConj, map_mul]
    group
  have he : Equivalence (TwConjugate θ) := ⟨hr, hs, ht⟩
  constructor
  · intro h
    have h1 : Quot.mk (TwConjugate θ) (Quot.out c) = Quot.mk _ d := by rw [Quot.out_eq, h]
    exact he.eqvGen_iff.1 (Quot.eqvGen_exact h1)
  · intro h
    rw [← Quot.sound h, Quot.out_eq]

section Adelic

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ}

theorem thetaA_ratGL (n : ℕ) (d : GL (Fin n) E) : thetaA E n (ratGL E n d) = ratGL E n (thetaE E n d) := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  rw [thetaR_val, ← map_inv]
  exact conjAd_algebraMap _

theorem discreteTopology_prodMap : DiscreteTopology ((ratGL E a).prodMap (ratGL E b)).range := by
  haveI := GlobalTheory.CompanionTheory.KerTwFin.discreteTopology_range (E := E) (n := a)
  haveI := GlobalTheory.CompanionTheory.KerTwFin.discreteTopology_range (E := E) (n := b)
  let f : ((ratGL E a).prodMap (ratGL E b)).range → (ratGL E a).range × (ratGL E b).range := fun z =>
    (⟨z.1.1, by obtain ⟨w, hw⟩ := z.2; exact ⟨w.1, congrArg Prod.fst hw⟩⟩,
     ⟨z.1.2, by obtain ⟨w, hw⟩ := z.2; exact ⟨w.2, congrArg Prod.snd hw⟩⟩)
  have hf : Continuous f := by
    refine Continuous.prodMk ?_ ?_
    · exact (continuous_fst.comp continuous_subtype_val).subtype_mk _
    · exact (continuous_snd.comp continuous_subtype_val).subtype_mk _
  have hi : Injective f := by
    intro z w h
    refine Subtype.ext (Prod.ext ?_ ?_)
    · exact congrArg (fun p => (p.1 : GA E a)) h
    · exact congrArg (fun p => (p.2 : GA E b)) h
  exact DiscreteTopology.of_continuous_injective hf hi

theorem finite_pair {φ : GA E a × GA E b → ℂ} (hφ : HasCompactSupport φ) {L : Set (GA E a × GA E b)} (hL : IsCompact L) :
    {d : GL (Fin a) E × GL (Fin b) E | ∃ x ∈ L,
      φ (twConj (thetaA E a) x.1 (ratGL E a d.1), twConj (thetaA E b) x.2 (ratGL E b d.2)) ≠ 0}.Finite := by
  have hθ₁ := GlobalTheory.CompanionTheory.KerTwFin.continuous_thetaA (E := E) (n := a)
  have hθ₂ := GlobalTheory.CompanionTheory.KerTwFin.continuous_thetaA (E := E) (n := b)
  have hL₁ : IsCompact (Prod.fst '' L) := hL.image continuous_fst
  have hL₂ : IsCompact (Prod.snd '' L) := hL.image continuous_snd
  have hS₁ : IsCompact (Prod.fst '' tsupport φ) := IsCompact.image hφ continuous_fst
  have hS₂ : IsCompact (Prod.snd '' tsupport φ) := IsCompact.image hφ continuous_snd
  have hK₁ := (hL₁.mul hS₁).mul (hL₁.image hθ₁).inv
  have hK₂ := (hL₂.mul hS₂).mul (hL₂.image hθ₂).inv
  refine ((GlobalTheory.CompanionTheory.KerTwFin.finite_ratGL_mem hK₁).prod (GlobalTheory.CompanionTheory.KerTwFin.finite_ratGL_mem hK₂)).subset ?_
  rintro ⟨d₁, d₂⟩ ⟨x, hx, h⟩
  have hs := subset_tsupport _ h
  constructor
  · change ratGL E a d₁ ∈ Prod.fst '' L * Prod.fst '' tsupport φ * (thetaA E a '' (Prod.fst '' L))⁻¹
    have hd : ratGL E a d₁ = x.1 * twConj (thetaA E a) x.1 (ratGL E a d₁) * (thetaA E a x.1)⁻¹ := by
      simp only [twConj]
      group
    rw [hd]
    exact Set.mul_mem_mul (Set.mul_mem_mul ⟨x, hx, rfl⟩ ⟨_, hs, rfl⟩)
      (Set.inv_mem_inv.2 ⟨x.1, ⟨x, hx, rfl⟩, rfl⟩)
  · change ratGL E b d₂ ∈ Prod.snd '' L * Prod.snd '' tsupport φ * (thetaA E b '' (Prod.snd '' L))⁻¹
    have hd : ratGL E b d₂ = x.2 * twConj (thetaA E b) x.2 (ratGL E b d₂) * (thetaA E b x.2)⁻¹ := by
      simp only [twConj]
      group
    rw [hd]
    exact Set.mul_mem_mul (Set.mul_mem_mul ⟨x, hx, rfl⟩ ⟨_, hs, rfl⟩)
      (Set.inv_mem_inv.2 ⟨x.2, ⟨x, hx, rfl⟩, rfl⟩)

theorem chiT_norm_le (τ : ℝ) {n : ℕ} (x : GA E n) : ‖(chiT τ x : ℂ)‖ ≤ 1 := by
  by_cases h : x ∈ cutSet E n τ <;> simp [chiT, h]

theorem mem_cutSet_of_chiT_ne_zero {τ : ℝ} {n : ℕ} {x : GA E n} (h : (chiT τ x : ℂ) ≠ 0) : x ∈ cutSet E n τ := by
  by_contra hx
  exact h (by simp [chiT, hx])

end Adelic

theorem unfold2_of (hM : Mahler) : Unfold2 := by
  intro E _ _ _ a b _ _ _ _ μ₁ _ μ₂ _ F₁ F₂ τ r φ hF₁ hF₂ hφ
  haveI := CuspidalL2GL.locallyCompactSpace_GA E a
  haveI := CuspidalL2GL.locallyCompactSpace_GA E b
  haveI := CuspidalL2GL.secondCountableTopology_GA E a
  haveI := CuspidalL2GL.secondCountableTopology_GA E b
  haveI : SigmaFinite μ₁ := sigmaFinite_of_locallyFinite
  haveI : SigmaFinite μ₂ := sigmaFinite_of_locallyFinite
  obtain ⟨hc₁, hi₁, C₁, hC₁, hs₁⟩ := hM E a τ
  obtain ⟨hc₂, hi₂, C₂, hC₂, hs₂⟩ := hM E b τ
  let ι : GL (Fin a) E × GL (Fin b) E →* GA E a × GA E b := (ratGL E a).prodMap (ratGL E b)
  let θ : Monoid.End (GA E a × GA E b) := (thetaA E a).prodMap (thetaA E b)
  let θR : Monoid.End (GL (Fin a) E × GL (Fin b) E) := (thetaE E a).prodMap (thetaE E b)
  haveI : DiscreteTopology ι.range := discreteTopology_prodMap
  haveI : Countable ι.range := by
    haveI : SecondCountableTopology ι.range := inferInstance
    exact (TopologicalSpace.separableSpace_iff_countable).1 inferInstance
  have hι : Injective ι :=
    GlobalTheory.CompanionTheory.KerTwFin.injective_ratGL.prodMap GlobalTheory.CompanionTheory.KerTwFin.injective_ratGL
  haveI : Countable (GL (Fin a) E × GL (Fin b) E) :=
    Injective.countable (f := ι.rangeRestrict) (fun x y h => hι (congrArg Subtype.val h))
  have hθ : ∀ r, ι (θR r) = θ (ι r) := fun r => Prod.ext (thetaA_ratGL a r.1).symm (thetaA_ratGL b r.2).symm
  have hFd : IsFundamentalDomain ι.range (F₁ ×ˢ F₂) (μ₁.prod μ₂) :=
    GlobalTheory.CompanionTheory.PairDom.isFundamentalDomain_range_prodMap μ₁ μ₂ (ratGL E a) (ratGL E b) F₁ F₂ hF₁ hF₂
  let cls : GL (Fin a) E × GL (Fin b) E → TwClass E a × TwClass E b := fun d => (Quot.mk _ d.1, Quot.mk _ d.2)
  let rep : TwClass E a × TwClass E b → GL (Fin a) E × GL (Fin b) E := fun c => (Quot.out c.1, Quot.out c.2)
  have hcls : ∀ c d, cls d = c ↔ TwConjugate θR (rep c) d := by
    rintro ⟨c₁, c₂⟩ ⟨d₁, d₂⟩
    constructor
    · intro h
      obtain ⟨g₁, h₁⟩ := (mk_eq_iff_twConjugate _ c₁ d₁).1 (congrArg Prod.fst h)
      obtain ⟨g₂, h₂⟩ := (mk_eq_iff_twConjugate _ c₂ d₂).1 (congrArg Prod.snd h)
      exact ⟨(g₁, g₂), Prod.ext h₁ h₂⟩
    · rintro ⟨g, hg⟩
      exact Prod.ext ((mk_eq_iff_twConjugate _ c₁ d₁).2 ⟨g.1, congrArg Prod.fst hg⟩)
        ((mk_eq_iff_twConjugate _ c₂ d₂).2 ⟨g.2, congrArg Prod.snd hg⟩)
  let H : TwClass E a × TwClass E b → Subgroup (GA E a × GA E b) := fun c =>
    (ratCent (Quot.out c.1)).prod (ratCent (Quot.out c.2))
  have hH : ∀ c g, g ∈ H c ↔ ∃ t, ι t = g ∧ twConj θR t (rep c) = rep c := by
    rintro c ⟨g₁, g₂⟩
    constructor
    · rintro ⟨⟨t₁, h₁, rfl⟩, ⟨t₂, h₂, rfl⟩⟩
      exact ⟨(t₁, t₂), rfl, Prod.ext h₁ h₂⟩
    · rintro ⟨t, ht, hc⟩
      exact ⟨⟨t.1, congrArg Prod.fst hc, congrArg Prod.fst ht⟩, ⟨t.2, congrArg Prod.snd hc, congrArg Prod.snd ht⟩⟩
  have hmχ : ∀ (n : ℕ) [MeasurableSpace (GA E n)] [BorelSpace (GA E n)], IsClosed (cutSet E n τ) →
      Measurable (chiT τ : GA E n → ℂ) := fun n _ _ h => measurable_one.indicator h.measurableSet
  have hχm : Measurable fun x : GA E a × GA E b => (chiT τ x.1 * chiT τ x.2 : ℂ) :=
    ((hmχ a hc₁).comp measurable_fst).mul ((hmχ b hc₂).comp measurable_snd)
  have hχb : ∀ x : GA E a × GA E b, ‖(chiT τ x.1 * chiT τ x.2 : ℂ)‖ ≤ 1 := fun x => by
    rw [norm_mul]
    exact mul_le_one₀ (chiT_norm_le τ _) (norm_nonneg _) (chiT_norm_le τ _)
  have hinv : ∀ (n : ℕ), (∀ g x, ratGL E n g * x ∈ cutSet E n τ ↔ x ∈ cutSet E n τ) → ∀ g (x : GA E n),
      (chiT τ (ratGL E n g * x) : ℂ) = chiT τ x := fun n h g x => by
    by_cases hx : x ∈ cutSet E n τ
    · simp [chiT, hx, (h g x).2 hx]
    · simp [chiT, hx, mt (h g x).1 hx]
  have hχi : ∀ (r : GL (Fin a) E × GL (Fin b) E) (x : GA E a × GA E b),
      (chiT τ (ι r * x).1 * chiT τ (ι r * x).2 : ℂ) = chiT τ x.1 * chiT τ x.2 := fun r x => by
    change (chiT τ (ratGL E a r.1 * x.1) * chiT τ (ratGL E b r.2 * x.2) : ℂ) = _
    rw [hinv a hi₁, hinv b hi₂]
  have hχK : ∀ x : GA E a × GA E b, (chiT τ x.1 * chiT τ x.2 : ℂ) ≠ 0 → ∃ r, ∃ k ∈ C₁ ×ˢ C₂, x = ι r * k := by
    intro x hx
    obtain ⟨_, ⟨r₁, rfl⟩, k₁, hk₁, e₁⟩ := Set.mem_mul.1 (hs₁ (mem_cutSet_of_chiT_ne_zero (left_ne_zero_of_mul hx)))
    obtain ⟨_, ⟨r₂, rfl⟩, k₂, hk₂, e₂⟩ := Set.mem_mul.1 (hs₂ (mem_cutSet_of_chiT_ne_zero (right_ne_zero_of_mul hx)))
    exact ⟨(r₁, r₂), (k₁, k₂), ⟨hk₁, hk₂⟩, Prod.ext e₁.symm e₂.symm⟩
  have hθc : Continuous θ := (GlobalTheory.CompanionTheory.KerTwFin.continuous_thetaA.comp continuous_fst).prodMk
    (GlobalTheory.CompanionTheory.KerTwFin.continuous_thetaA.comp continuous_snd)
  have hφm : ∀ d, Measurable fun x => φ (twConj θ x (ι d)) := fun d =>
    (hφ.cont.comp ((continuous_inv.mul continuous_const).mul hθc)).measurable
  haveI : T2Space (GA E a × GA E b) := by
    set_option synthInstance.maxHeartbeats 200000 in
      exact inferInstance
  obtain ⟨B, hB⟩ := hφ.supp.exists_bound_of_continuous hφ.cont
  haveI : SigmaFinite (μ₁.prod μ₂) := Measure.prod.instSigmaFinite
  haveI : SFinite (μ₁.prod μ₂) := MeasureTheory.instSFiniteOfSigmaFinite
  have key := unfold_abs (μ := μ₁.prod μ₂) (ι := ι) (θ := θ) (θR := θR) (cls := cls) (rep := rep) (H := H)
    (χ := fun x => chiT τ x.1 * chiT τ x.2) (φ := φ) hι hθ hFd hcls hH hχm hχb hχi (hC₁.prod hC₂) hχK hφm hB
    (fun L hL => finite_pair hφ.supp hL)
  exact key

end GlobalTheory.CompanionTheory.TwUnfold

end
end

section

noncomputable section

open NumberField IsDedekindDomain Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR
open Formalism.UG (cT)
open scoped TensorProduct
open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups (extH tensNU tensNU_tmul)

namespace GlobalTheory.CompanionTheory.KFin

section Step

variable {F E R R' : Type} [Field F] [Field E] [Algebra F E] [CommRing R] [Algebra F R]
  [CommRing R'] [Algebra F R'] (j : R →ₗ[F] R') (hj : ∀ a b, j (a * b) = j a * j b)

theorem tensNU_mul_inclR (u : R ⊗[F] E) (e : E) :
    tensNU j hj u * inclR (F := F) R' e = tensNU j hj (u * inclR (F := F) R e) := by
  induction u using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [add_mul, map_add (f := _), hx, hy]
  | tmul a e' => simp [inclR, Algebra.TensorProduct.tmul_mul_tmul]

theorem map_tensNU_mul_inclR {a b c : Type} [Fintype b] (A : Matrix a b (R ⊗[F] E)) (X : Matrix b c E) :
    A.map (tensNU j hj) * X.map (inclR (F := F) R') = (A * X.map (inclR (F := F) R)).map (tensNU j hj) := by
  ext r s

  simp only [Matrix.mul_apply, Matrix.map_apply, tensNU_mul_inclR, map_sum]

theorem inclR_mul_map_tensNU {a b c : Type} [Fintype b] (X : Matrix a b E) (A : Matrix b c (R ⊗[F] E)) :
    X.map (inclR (F := F) R') * A.map (tensNU j hj) = (X.map (inclR (F := F) R) * A).map (tensNU j hj) := by
  ext r s

  simp only [Matrix.mul_apply, Matrix.map_apply, mul_comm (inclR (F := F) R' _), mul_comm (inclR (F := F) R _),
  tensNU_mul_inclR, map_sum]

theorem mat_extH_eq_add (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (g : HA R σ J) :
    (HA.mat R' σ J (extH σ J j hj g)).1 = 1 + ((HA.mat R σ J g).1 - 1).map (tensNU j hj) := by
  ext r s
  rw [GlobalTheory.AutFunCompare.mat_extH]
  by_cases h : r = s
  · subst h
    simp [map_sub]
    ring
  · simp [Matrix.one_apply, h]

theorem extH_stab (σ : E →ₐ[F] E) {n r : ℕ} (J : Matrix (Fin n) (Fin n) E) (g : HA R σ J)
    (X : Matrix (Fin n) (Fin r) E) (B : Matrix (Fin r) (Fin r) (R ⊗[F] E)) (hB : B.BlockTriangular id)
    (h : (HA.mat R σ J g).1 * X.map (inclR (F := F) R) = X.map (inclR (F := F) R) * B) :
    ∃ B' : Matrix (Fin r) (Fin r) (R' ⊗[F] E), B'.BlockTriangular id ∧
      (HA.mat R' σ J (extH σ J j hj g)).1 * X.map (inclR (F := F) R') = X.map (inclR (F := F) R') * B' := by
  refine ⟨1 + (B - 1).map (tensNU j hj), ?_, ?_⟩
  · intro a b hab
    have hne : a ≠ b := fun e => by subst e; exact lt_irrefl _ hab
    have h0 : B a b = 0 := hB hab
    simp [Matrix.one_apply, hne, h0]
  · rw [mat_extH_eq_add, Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, map_tensNU_mul_inclR,
      inclR_mul_map_tensNU, Matrix.sub_mul, Matrix.mul_sub, h, Matrix.one_mul, Matrix.mul_one]

end Step

theorem emb_mem_minPar {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {r : ℕ} {X Y : Matrix (Fin n) (Fin r) E}
    (v : HeightOneSpectrum (𝓞 F)) (p : GLoc σ J v) (B : Matrix (Fin r) (Fin r) (Fv F v ⊗[F] E))
    (hB : B.BlockTriangular id)
    (h : (matHom _ σ J p).1 * X.map (inclR (F := F) (Fv F v)) = X.map (inclR (F := F) (Fv F v)) * B) :
    emb σ J v p ∈ minPar σ J X := by
  obtain ⟨B₁, hB₁, h₁⟩ := extH_stab (singleFin v) (singleFin_mul v) σ J p X B hB h
  obtain ⟨B₂, hB₂, h₂⟩ := extH_stab (R' := AF F) (LinearMap.inr F (Ainf F) (Af F))
    (fun _ _ => Prod.ext (mul_zero _).symm rfl) σ J _ X B₁ hB₁ h₁
  exact ⟨B₂, hB₂, h₂⟩

end GlobalTheory.CompanionTheory.KFin

end
end

section

open HeckeCharacterZeroLocus.SiegelWeilU NumberField MeasureTheory
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.Hypotheses₂.SdExistN

theorem exists_sdW_tuples : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ ψ : AddChar (AF F) ℂ, IsCharAF F ψ → ∀ n : ℕ, ∃ μ : Measure (Fin n → Fin M → AF F ⊗[F] E), SdW F E σ M J (AF F) ψ n μ := by
  intro F E _ _ _ _ _ σ hCM M J hJ ψ hψ n
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  let b := Module.finBasis F E
  obtain ⟨B, hsym, hdet, -, hR'⟩ :=
    GlobalTheory.CompanionTheory.SW.TraceCoord.exists_trace_coord F E σ hCM M J hJ _ b
  obtain ⟨h1, h2, h3, h4, -, -, hcc, hBor, -, -⟩ := GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hCM (AF F)
  haveI := h1
  haveI : BorelSpace (AF F ⊗[F] E) := ⟨rfl⟩
  haveI := hBor n M
  have hc : IsHomeomorph (GlobalTheory.CompanionTheory.SW.SdTuples.cf (F := F) (E := E) (AF F) b) := hcc _ b
  have hsym' : (Matrix.blockDiagonal fun _ : Fin n => B).IsSymm := by
    unfold Matrix.IsSymm
    rw [Matrix.blockDiagonal_transpose]
    simp only [hsym.eq]
  have hdet' : (Matrix.blockDiagonal fun _ : Fin n => B).det ≠ 0 := by
    rw [Matrix.det_blockDiagonal]
    exact Finset.prod_ne_zero_iff.mpr fun _ _ => hdet
  obtain ⟨μ, hμ⟩ := GlobalTheory.CompanionTheory.Hypotheses₂.SdExist.exists_selfDual_form ψ hψ _ hsym' hdet'
    (GlobalTheory.CompanionTheory.SW.SdTuples.tupE hc n M)
  refine ⟨μ, ?_⟩
  unfold SdW
  have hf : (fun X Y : Fin n → Fin M → AF F ⊗[F] E => ψ (BR (AF F) σ J X Y)) = fun X Y =>
      ψ (dotProduct (GlobalTheory.CompanionTheory.SW.SdTuples.tupE hc n M X) (Matrix.mulVec
        ((Matrix.blockDiagonal fun _ : Fin n => B).map (algebraMap F (AF F)))
        (GlobalTheory.CompanionTheory.SW.SdTuples.tupE hc n M Y))) := by
    funext X Y
    rw [← GlobalTheory.CompanionTheory.SW.SdTuples.BR_eq hc J B (hR' (AF F)).1 X Y]
  rw [hf]
  exact hμ

end GlobalTheory.CompanionTheory.Hypotheses₂.SdExistN
end
