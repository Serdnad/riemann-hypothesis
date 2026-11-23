module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ModuliModelUltrametricPoints
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle204
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle123
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle042
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle026
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.CoeNonzeroLocusCanonicalEqComplRange
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle012
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle102
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle631
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle655
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle628
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle656
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle660
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle658
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
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
import Mathlib.RingTheory.WittVector.IsPoly
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.IsPrecompleteOfBasis
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FnAlgClosedOfFixedPoints
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AmpleOnAbelianBase
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Degenerations.MorAlgSt
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle002
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle532
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
public import Mathlib.NumberTheory.NumberField.CMField
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle005
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.CanonGenIsGen
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
import Formalism.SharpRestriction.Divisibility.AbelianOpenPart.AbelianAt

@[expose] public section

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace Polynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef

namespace GlobalTheory.ResLift

open ReciprocityTheory.ChartRestriction.G.Semi.Nb

theorem irreducible_adjoinRoot {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (f : V[X])
    (hf : f.Monic) (hg : Irreducible (f.map (residue V))) [IsDomain (AdjoinRoot f)] [IsLocalRing (AdjoinRoot f)]
    [IsDiscreteValuationRing (AdjoinRoot f)] {ϖ : V} (hϖ : Irreducible ϖ) :
    Irreducible (algebraMap V (AdjoinRoot f) ϖ) := by
  rw [IsDiscreteValuationRing.irreducible_iff_uniformizer, maxEq f hf hg, hϖ.maximalIdeal_eq, Ideal.map_span,
    Set.image_singleton]

theorem exists_lift (n : ℕ) : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    [IsAdicComplete (maximalIdeal V) V]
    (k'' : Type) [Field k''] [Algebra (ResidueField V) k'']
    [FiniteDimensional (ResidueField V) k''], Module.finrank (ResidueField V) k'' = n →
    ∃ (V'' : Type) (_ : CommRing V'') (_ : IsDomain V'') (_ : IsDiscreteValuationRing V'')
      (_ : IsAdicComplete (maximalIdeal V'') V'') (_ : Algebra V V''),
      Module.Finite V V'' ∧ Function.Injective (algebraMap V V'') ∧
      (∀ ϖ : V, Irreducible ϖ → Irreducible (algebraMap V V'' ϖ)) ∧
      ∃ (_ : IsLocalHom (algebraMap V V'')) (e : k'' ≃+* ResidueField V''),
        e.toRingHom.comp (algebraMap (ResidueField V) k'') =
          ResidueField.map (algebraMap V V'') := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro V' _ _ _ _ k'' _ _ _ hn
  by_cases hs : Function.Surjective (algebraMap (ResidueField V') k'')
  · have hb : Function.Bijective (algebraMap (ResidueField V') k'') :=
      ⟨(algebraMap (ResidueField V') k'').injective, hs⟩
    refine ⟨V', inferInstance, inferInstance, inferInstance, inferInstance, Algebra.id V',
      Module.Finite.self V', Function.injective_id, fun ϖ h => h, ?_, (RingEquiv.ofBijective _ hb).symm, ?_⟩
    · change IsLocalHom (RingHom.id V'); infer_instance
    · ext x
      change _ = ResidueField.map (RingHom.id V') x
      rw [ResidueField.map_id]
      exact (RingEquiv.ofBijective _ hb).symm_apply_apply x
  · obtain ⟨α, hα⟩ : ∃ α : k'', α ∉ Set.range (algebraMap (ResidueField V') k'') := by
      by_contra h
      push_neg at h
      exact hs h
    have hint : IsIntegral (ResidueField V') α := .of_finite (ResidueField V') α
    have hmon := minpoly.monic hint
    have hirr := minpoly.irreducible hint
    obtain ⟨f, hfg, hdeg, hf⟩ := exists_monic_lift (minpoly (ResidueField V') α) hmon
    have hg : Irreducible (f.map (residue V')) := hfg ▸ hirr
    have := isDomain f hf hg
    have := isLocal f hf hg
    have := dvr f hf hg
    have := complete f hf hg
    have := locHom f hf hg
    have := finite f hf
    have haev : Polynomial.aeval α (f.map (residue V')) = 0 := by
      rw [hfg]; exact minpoly.aeval _ α
    let ψ : AdjoinRoot (f.map (residue V')) →ₐ[ResidueField V'] k'' :=
      AdjoinRoot.liftAlgHom _ (Algebra.ofId _ _) α (by rwa [Polynomial.aeval_def] at haev)
    letI : Algebra (ResidueField (AdjoinRoot f)) k'' :=
      (ψ.toRingHom.comp (resEquiv f hf hg).toRingHom).toAlgebra
    have : Fact (Irreducible (f.map (residue V'))) := ⟨hg⟩
    letI : Algebra (AdjoinRoot (f.map (residue V'))) k'' := ψ.toRingHom.toAlgebra
    have : IsScalarTower (ResidueField V') (AdjoinRoot (f.map (residue V'))) k'' :=
      IsScalarTower.of_algebraMap_eq fun x => (ψ.commutes x).symm
    have hL : Module.finrank (ResidueField V') (AdjoinRoot (f.map (residue V'))) =
        (minpoly (ResidueField V') α).natDegree := by
      rw [(AdjoinRoot.powerBasis hg.ne_zero).finrank, AdjoinRoot.powerBasis_dim, hfg]
    have hd1 : (minpoly (ResidueField V') α).natDegree ≠ 1 := fun h =>
      hα (minpoly.natDegree_eq_one_iff.1 h)
    have hd0 : 0 < (minpoly (ResidueField V') α).natDegree := minpoly.natDegree_pos hint
    have : FiniteDimensional (AdjoinRoot (f.map (residue V'))) k'' :=
      Module.Finite.of_restrictScalars_finite (ResidueField V') _ k''
    have hmul := Module.finrank_mul_finrank (ResidueField V') (AdjoinRoot (f.map (residue V'))) k''
    have hAL : Module.finrank (ResidueField (AdjoinRoot f)) k'' =
        Module.finrank (AdjoinRoot (f.map (residue V'))) k'' :=
      Algebra.finrank_eq_of_equiv_equiv (resEquiv f hf hg) (RingEquiv.refl k'') rfl
    have hpos : 0 < Module.finrank (AdjoinRoot (f.map (residue V'))) k'' := Module.finrank_pos
    have : FiniteDimensional (ResidueField (AdjoinRoot f)) k'' :=
      Module.finite_of_finrank_pos (hAL ▸ hpos)
    have hlt : Module.finrank (ResidueField (AdjoinRoot f)) k'' < n := by
      rw [hAL, ← hn, ← hmul, hL]
      calc Module.finrank (AdjoinRoot (f.map (residue V'))) k''
          < 2 * Module.finrank (AdjoinRoot (f.map (residue V'))) k'' := by omega
        _ ≤ _ := Nat.mul_le_mul_right _ (by omega)
    obtain ⟨V'', i1, i2, i3, i4, i5, hfin, hinj, hirr'', hloc, e2, he2⟩ :=
      ih _ hlt (AdjoinRoot f) k'' rfl
    letI : Algebra V' V'' := ((algebraMap (AdjoinRoot f) V'').comp (algebraMap V' (AdjoinRoot f))).toAlgebra
    have : IsScalarTower V' (AdjoinRoot f) V'' := IsScalarTower.of_algebraMap_eq fun _ => rfl
    have hlc : IsLocalHom (algebraMap V' V'') := by
      change IsLocalHom ((algebraMap (AdjoinRoot f) V'').comp (algebraMap V' (AdjoinRoot f)))
      infer_instance
    refine ⟨V'', i1, i2, i3, i4, inferInstance, Module.Finite.trans (AdjoinRoot f) V'',
      hinj.comp (inj f hf hg), fun ϖ hϖ => hirr'' _ (irreducible_adjoinRoot f hf hg hϖ), hlc, e2, ?_⟩
    have h1 : (algebraMap (ResidueField (AdjoinRoot f)) k'').comp
        (ResidueField.map (algebraMap V' (AdjoinRoot f))) = algebraMap (ResidueField V') k'' := by
      change ψ.toRingHom.comp ((resEquiv f hf hg).toRingHom.comp
        (ResidueField.map (algebraMap V' (AdjoinRoot f)))) = _
      rw [resEquiv_comp f hf hg, ← AdjoinRoot.algebraMap_eq]
      exact ψ.comp_algebraMap
    change e2.toRingHom.comp (algebraMap (ResidueField V') k'') =
      ResidueField.map ((algebraMap (AdjoinRoot f) V'').comp (algebraMap V' (AdjoinRoot f)))
    rw [ResidueField.map_comp, ← h1, ← RingHom.comp_assoc, he2]

end GlobalTheory.ResLift

namespace GlobalTheory.TorRef

theorem exists_unif_unram : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V : Type) [CommRing V] [IsDomain V]
    [IsLocalRing V], CDvr V → ∀ ϖ : V, Irreducible ϖ → ∀ (t : SAB H (Sp V)), PolAt t (jK V) →
    ∃ (V' : Type) (_ : CommRing V') (_ : IsDomain V') (_ : IsLocalRing V') (f : V →+* V'),
      CDvr V' ∧ Function.Injective f ∧ IsLocalHom f ∧ Irreducible (f ϖ) ∧
      ∃ (t' : SAB H (Sp V')) (_ : SABMap t' t (spMap f)), Nonempty (PELUnif (maximalIdeal V') t') := by
  intro E _ _ _ H V _ _ _ hV ϖ hϖ t hp
  obtain ⟨hd, hc, hz⟩ := (cDvr_iff V).1 hV
  let Ω := AlgebraicClosure (ResidueField V)
  obtain ⟨s, hs, h⟩ := GlobalTheory.Ex.UnifModel.exists_finite_split (algebraMap (ResidueField V) Ω) t.G t.semi
  have := hs.to_subtype
  let k'' := IntermediateField.adjoin (ResidueField V) s
  have : FiniteDimensional (ResidueField V) k'' :=
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  obtain ⟨W, _, _, _, hcW, _, -, hinj, hirr, hloc, e, he⟩ :=
    GlobalTheory.ResLift.exists_lift _ V k'' rfl
  have : IsLocalRing W := inferInstance
  have hzW : CharZero W := charZero_of_injective_algebraMap hinj
  let β : ResidueField W →+* Ω := k''.val.toRingHom.comp e.symm.toRingHom
  have hβ : β.comp (ResidueField.map (algebraMap V W)) = algebraMap (ResidueField V) Ω := by
    rw [← he]
    ext x
    simp [β]
  have hsp := h W (algebraMap V W) β hβ fun x hx =>
    ⟨e ⟨x, IntermediateField.subset_adjoin _ _ hx⟩, by simp [β]⟩
  open scoped CategoryTheory.Obj in
    let f := spMap (algebraMap V W)
    have hC := Out.CubePf.cubePull
    have hsemi : IsSemiAbelian ((Over.pullback f).obj t.G) := by
      refine { comm := ?_, smooth := ?_, separated := ?_, quasiCompact := ?_, geomConnected := ?_, fibres := ?_ }
      · have := t.semi.comm
        infer_instance
      · have := t.semi.smooth
        change Smooth (pullback.snd t.G.hom f)
        infer_instance
      · have := t.semi.separated
        change IsSeparated (pullback.snd t.G.hom f)
        infer_instance
      · have := t.semi.quasiCompact
        change QuasiCompact (pullback.snd t.G.hom f)
        infer_instance
      · have := t.semi.geomConnected
        change GeometricallyConnected (pullback.snd t.G.hom f)
        infer_instance
      · intro Ω _ _ q
        obtain ⟨A⟩ := t.semi.fibres Ω (q ≫ f)
        exact ⟨torusExtOfIso (pullCompIso q f t.G) A⟩
    have hp : ∃ (PP' : RigLB ((Over.pullback f).obj t.G)) (cub : CubicalStr _ PP') (sym : PP'.IsSymmetric) (adj : _) (prim : _)
        (m : SABMap ⟨(Over.pullback f).obj t.G, hsemi, OAct.pullback f t.G t.act, PP', cub,
          sym, adj, prim⟩ t f), m.φ = pullback.fst t.G.hom f := by
      have h := isGrpPullback_pullback t.G f
      obtain ⟨hL, hr, ⟨c', hc'⟩, hs⟩ := hC (Sp V) (Sp W) t.G _ (cubeMapOf h) t.PP t.cub
      have hact : ∀ a, ((OAct.pullback f t.G t.act).act a).left ≫ pullback.fst t.G.hom f =
          pullback.fst t.G.hom f ≫ (t.act.act a).left := fun a => pullback.lift_fst _ _ _
      have pa : ∀ {T : Over (Sp W)} (x : T ⟶ (Over.pullback f).obj t.G) a,
          pushPt h.1.w (x ≫ (OAct.pullback f t.G t.act).act a) = pushPt h.1.w x ≫ t.act.act a := fun x a =>
        Over.OverMorphism.ext (by
          show (x.left ≫ _) ≫ _ = (x.left ≫ _) ≫ _
          rw [Category.assoc, hact, Category.assoc])
      refine ⟨(cubeMapOf h).rigLB t.PP hL hr, c', hs t.sym, fun a => ?_, ?_, ⟨cubeMapOf h, h, rfl, hact, hc'⟩, rfl⟩
      · let U := CartesianMonoidalCategory.lift (pushPt h.1.w (CartesianMonoidalCategory.fst ((Over.pullback f).obj t.G) ((Over.pullback f).obj t.G)))
          (pushPt h.1.w (CartesianMonoidalCategory.snd ((Over.pullback f).obj t.G) ((Over.pullback f).obj t.G)))
        refine LBIso.chartPull (chartPullLinComb t.PP.L _ _ _ _ U.left fun I => psum_push h _ _ U (fun i => ?_) I.down)
          (chartPullLinComb t.PP.L _ _ _ _ U.left fun I => psum_push h _ _ U (fun i => ?_) I.down) (t.adj a)
        · fin_cases i
          · exact (pa _ a).trans (by simp [U])
          · simp [U]
        · fin_cases i
          · simp [U]
          · exact (pa _ _).trans (by simp [U])
      · let U := pushPt h.1.w (𝟙 ((Over.pullback f).obj t.G))
        refine LBIso.chartPull (chartPullPull t.PP.L _)
          (chartPullLinComb t.PP.L _ _ _ _ U.left fun I => psum_push h _ _ U (fun i => ?_) I.down) t.prim
        fin_cases i
        · simp [U]
        · exact (congrArg (pushPt h.1.w) (Category.id_comp _).symm).trans (pa _ _)
    obtain ⟨_, _, _, _, _, m, -⟩ := hp
    have j : Function.Injective ((algebraMap W (FractionRing W)).comp (algebraMap V W)) :=
      (IsFractionRing.injective W _).comp hinj
    let g : FractionRing V →+* FractionRing W := IsFractionRing.lift j
    have hp' := GlobalTheory.DatUniq.polAt_pull m hp (jK W) (spMap g)
      ((GlobalTheory.Ex.UnifModel.spMap_comp (IsFractionRing.lift_algebraMap j)).trans
        (GlobalTheory.Ex.UnifModel.spMap_comp fun _ => rfl).symm)
    have hW : CDvr W := (cDvr_iff W).2 ⟨inferInstance, hcW, hzW⟩
    obtain ⟨P, -⟩ := GlobalTheory.LN.uDvrSt_holds E H W hW _ hp' hsp
    exact ⟨W, inferInstance, inferInstance, inferInstance, algebraMap V W, hW, hinj, hloc, hirr ϖ hϖ, _, m, ⟨P⟩⟩

end GlobalTheory.TorRef
end
end

section

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef

noncomputable section

namespace GlobalTheory.GenPush

theorem isIntegral_of_isIso_comp {A B C D : CommRingCat.{0}} (k : A ⟶ B) (f : B ⟶ C) (m : C ⟶ D) [IsIso k]
    [IsIso m] (h : (k ≫ f ≫ m).hom.IsIntegral) : f.hom.IsIntegral := by
  have e : f = inv k ≫ (k ≫ f ≫ m) ≫ inv m := by simp
  rw [e, CommRingCat.hom_comp, CommRingCat.hom_comp]
  refine RingHom.IsIntegral.trans _ _ ?_ (RingHom.IsIntegral.trans _ _ h ?_)
  · exact RingHom.isIntegral_of_surjective _ (ConcreteCategory.bijective_of_isIso (inv k)).2
  · exact RingHom.isIntegral_of_surjective _ (ConcreteCategory.bijective_of_isIso (inv m)).2

theorem isIntegral_app_of_universallyClosed {Z₁ Z₂ : Scheme.{0}} (ρ : Z₁ ⟶ Z₂) [UniversallyClosed ρ]
    (U : Z₂.Opens) (hU : IsAffineOpen U) : (ρ.app U).hom.IsIntegral := by
  have : IsAffine U.toScheme := hU
  have h := isIntegral_appTop_of_universallyClosed (ρ ∣_ U)
  rw [morphismRestrict_appTop] at h
  have e : U.ι ''ᵁ ⊤ = U := by simp
  rw [ρ.app_eq e, Category.assoc, Category.assoc, ← Functor.map_comp] at h
  simp only [eqToHom_op, eqToHom_map, eqToHom_trans] at h
  have hi : ∀ {A B : CommRingCat.{0}} (p : A = B), IsIso (eqToHom p) := fun p => by
    subst p; rw [eqToHom_refl]; infer_instance
  refine @isIntegral_of_isIso_comp _ _ _ _ _ _ _ ?_ ?_ h
  · exact hi _
  · exact hi _

theorem exists_app_eq_of_isIntegralElem {T Z : Scheme.{0}} [GlobalTheory.IsNormalScheme Z] [IsLocallyNoetherian Z]
    (j : T ⟶ Z) [IsOpenImmersion j] (hj : Dense (Set.range j)) (U : Z.Opens)
    (s : Γ(T, j ⁻¹ᵁ U)) (hs : (j.app U).hom.IsIntegralElem s) : ∃ h : Γ(Z, U), j.app U h = s :=
  GlobalTheory.T.exists_section_extending_of_dense_openImmersion j hj U s fun u hu => GlobalTheory.T.exists_local_section_of_isIntegralElem_normal_scheme j hj U s hs u hu

section Models

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l}

end Models

end GlobalTheory.GenPush
end
end

section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef
open Cartier

theorem EffCartierData.keepsRegular_of_dense {X' N : Scheme.{0}} (D : EffCartierData X')
    (ν : N ⟶ X') (hN : ∀ y : N, IsDomain (N.presheaf.stalk y))
    (hd : Dense {z : N | ν z ∉ D.idealSheaf.support}) : D.KeepsRegular ν := by
  intro i
  refine isRegularFn_iff_germ.2 fun y hy => ?_
  haveI := hN y
  refine mem_nonZeroDivisors_of_ne_zero fun h0 => ?_
  have e : (N.presheaf.germ (ν ⁻¹ᵁ D.U i) y hy).hom ((ν.app (D.U i)).hom (D.f i)) =
      (N.presheaf.germ (ν ⁻¹ᵁ D.U i) y hy).hom 0 := by rw [h0, map_zero]
  obtain ⟨W, hW, i₁, i₂, e'⟩ := N.presheaf.germ_eq y hy hy _ _ e
  obtain ⟨z, hzW, hzO⟩ := hd.inter_open_nonempty W W.isOpen ⟨y, hW⟩
  haveI := hN z
  have hzU : z ∈ ν ⁻¹ᵁ D.U i := i₁.le hzW
  have hz0 : (N.presheaf.germ _ z hzU).hom ((ν.app (D.U i)).hom (D.f i)) = 0 := by
    have := congrArg (N.presheaf.germ W z hzW).hom e'
    simpa using this
  have hunit : IsUnit ((X'.presheaf.germ (D.U i) (ν z) hzU).hom (D.f i)) := by
    have h1 : ν z ∈ X'.basicOpen (D.f i) := by
      by_contra h
      exact hzO ((D.mem_support_iff i hzU).2 h)
    exact (X'.mem_basicOpen _ _ hzU).1 h1
  have hu := hunit.map (ν.stalkMap z).hom
  rw [← EffCartierData.germ_app ν (D.f i) z hzU, hz0] at hu
  exact not_isUnit_zero hu

end GlobalTheory

namespace GlobalTheory

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef

end GlobalTheory
end
end

section

open Matrix GlobalTheory.RedTh NumberField GlobalTheory.PolFan ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.RedTh

theorem adjoint_weighted_sq_trace : ∀ (n : ℕ) (A A' : Matrix (Fin n) (Fin n) ℤ) (d : Fin n → ℝ) (u v : Matrix (Fin n) (Fin n) ℝ), (∀ i, 0 < d i) → v * u = 1 → u * v = 1 → (A.map (Int.cast : ℤ → ℝ))ᵀ * gram d u = gram d u * A'.map (Int.cast : ℤ → ℝ) → (∀ p q, d p * (u * A.map (Int.cast : ℤ → ℝ) * v) p q = d q * (u * A'.map (Int.cast : ℤ → ℝ) * v) q p) ∧ (∑ p, ∑ q, d p / d q * (u * A.map (Int.cast : ℤ → ℝ) * v) p q ^ 2 = (((A' * A).trace : ℤ) : ℝ)) ∧ ∑ p, ∑ q, d p / d q * (u * A'.map (Int.cast : ℤ → ℝ) * v) p q ^ 2 = (((A' * A).trace : ℤ) : ℝ) := by
  intro n A A' d u v hd hvu huv h
  set a := A.map (Int.cast : ℤ → ℝ) with ha
  set a' := A'.map (Int.cast : ℤ → ℝ) with ha'
  have key : (u * a * v)ᵀ * diagonal d = diagonal d * (u * a' * v) := by
    have h2 := congrArg (fun M => vᵀ * M * v) h
    simp only [gram] at h2
    have e1 : vᵀ * (aᵀ * (uᵀ * diagonal d * u)) * v = (u * a * v)ᵀ * diagonal d * (u * v) := by
      simp only [transpose_mul, Matrix.mul_assoc]
    have e2 : vᵀ * (uᵀ * diagonal d * u * a') * v = (u * v)ᵀ * diagonal d * (u * a' * v) := by
      simp only [transpose_mul, Matrix.mul_assoc]
    rw [e1, e2, huv] at h2
    simpa using h2
  have c1 : ∀ p q, d p * (u * a * v) p q = d q * (u * a' * v) q p := by
    intro p q
    have := congrFun (congrFun key q) p
    simp only [mul_diagonal, diagonal_mul, transpose_apply] at this
    linarith
  have htr : ∑ p, ∑ q, (u * a' * v) q p * (u * a * v) p q = (((A' * A).trace : ℤ) : ℝ) := by
    have e : ∑ p, ∑ q, (u * a' * v) q p * (u * a * v) p q = ((u * a' * v) * (u * a * v)).trace := by
      rw [Finset.sum_comm]; simp [Matrix.trace, Matrix.mul_apply]
    rw [e]
    have : (u * a' * v) * (u * a * v) = u * (a' * a) * v := by
      rw [show (u * a' * v) * (u * a * v) = u * a' * (v * u) * a * v by simp only [Matrix.mul_assoc], hvu]
      simp only [Matrix.mul_one, Matrix.mul_assoc]
    rw [this, Matrix.trace_mul_comm, ← Matrix.mul_assoc, hvu, Matrix.one_mul]
    rw [ha, ha']
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.map_apply]
    push_cast; rfl
  refine ⟨c1, ?_, ?_⟩
  · rw [← htr]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
    have hq := (hd q).ne'
    rw [div_mul_eq_mul_div, div_eq_iff hq, sq, ← mul_assoc, c1 p q]; ring
  · rw [← htr, Finset.sum_comm]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
    have hp := (hd p).ne'
    rw [div_mul_eq_mul_div, div_eq_iff hp, sq, ← mul_assoc, ← c1 p q]; ring

end GlobalTheory.RedTh
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_holomorphic_fibre_exponentials_near_centre : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (σ : c.F →+* ℂ) (n : ℕ) (e0 : OpenPartialHomeomorph (CxPts (genStr Z) σ) (Fin n → ℂ)), (0 : Fin n → ℂ) ∈ e0.target → IsHolTo e0.target (fun z => (e0.symm z).1) → ∃ (g : ℕ) (ρ : ℝ) (ex : ExpMaps Z σ g), 0 < ρ ∧ Metric.ball 0 ρ ⊆ e0.target ∧ IsHolTo (Metric.ball 0 ρ ×ˢ Set.univ) (fun zw : (Fin n → ℂ) × (Fin g → ℂ) => (ex (e0.symm zw.1) zw.2).left) ∧ ∀ x ∈ e0.source, ‖e0 x‖ < ρ → Function.Surjective (ex x) ∧ IsExpAt Z.t (x.1 ≫ genι Z) (ex x) := by
  first | exact @GlobalTheory.ShFam.Hor.LogCh.exists_expMaps_near_chart_centre | exact GlobalTheory.ShFam.Hor.LogCh.exists_expMaps_near_chart_centre | (intros; apply GlobalTheory.ShFam.Hor.LogCh.exists_expMaps_near_chart_centre <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.ProjSpace GlobalTheory.FlagEmb
open Formalism.MainNotions.DIV.Cons (intO)

namespace GlobalTheory.FlagEmb

theorem span_plk_uvec_eq_top {X : Scheme.{0}} {T : Type} {m : T → ℕ} {M : ℕ} {U : X.affineOpens}
    {c D : Let m → Fin (M + 1) → Γ(X, U.1)} (h : LeftInv D c) (w : Pm m) (en : En m) :
    Ideal.span (Set.range (plk (uvec c w) en.2.1)) = ⊤ :=
  (Ideal.eq_top_iff_one _).2 (Ideal.mem_span_range_iff_exists_fun.2 ⟨_,
    (GlobalTheory.T.cauchyBinet_plucker_and_cellCoordinates.2 T m (CR m U) M _ _ w MvPolynomial.X
      (h.map (MvPolynomial.C : Γ(X, U.1) →+* CR m U))).1 en.1 en.2.1 en.2.2⟩)

theorem exists_isPlk : ∀ (O K : Type) [CommRing O] [Field K] (β : O →+* K) (X : Scheme.{0}) (s : X ⟶ Sp O)
    (T : Type) [Finite T] (m : T → ℕ) (M : ℕ) (B : Type) (V : B → X.affineOpens) (α : ∀ b, K →+* Γ(X, (V b).1))
    (c D : ∀ b, Let m → Fin (M + 1) → Γ(X, (V b).1)), IsProjOver s → IsCover β s V α c D →
    ∃ (P : Scheme.{0}) (p0 : P ⟶ X) (p : ∀ en : En m, P ⟶ PSpace O (plN M en.1))
      (h : ∀ b, Pm m → (Sp (CR m (V b)) ⟶ P)), IsPlk β s V α c p0 p h := by
  intro O K _ _ β X s T _ m M B V α c D hs hC
  obtain ⟨P, p0, p, hP, hp, univ⟩ := GlobalTheory.T.exists_isProjOver_finite_fibreProduct O (En m) X s (fun en => PSpace O (plN M en.1))
    (fun en => PSpace.str O _) hs fun en => ⟨_, 𝟙 _, inferInstance, Category.id_comp _⟩
  have hb : ∀ b, cbase m (V b) ≫ s =
      spMap ((MvPolynomial.C : _ →+* CR m (V b)).comp ((α b).comp β)) := fun b => by
    rw [cbase, Category.assoc, hC.ovr b, ← Spec.map_comp]
    rfl
  have pt_str : ∀ {A : Type} [CommRing A] {N : ℕ} (c : O →+* A)
      (v : Fin (N + 1) → A) (hv : Ideal.span (Set.range v) = ⊤),
      pt c v hv ≫ PSpace.str O N = spMap c := by
    intro A _ N c v hv
    rw [pt, PSpace.str, ProjPoint.ofHom_toSpecZero_assoc, ← Spec.map_comp]
    congr 1
    ext1
    exact RingHom.ext fun r => MvPolynomial.eval₂Hom_C c v r
  choose h hh using fun (b : B) (w : Pm m) => (univ _ (cbase m (V b))
    (fun en => pt ((MvPolynomial.C : _ →+* CR m (V b)).comp ((α b).comp β)) (plk (uvec (c b) w) en.2.1)
      (span_plk_uvec_eq_top (hC.inv b) w en))
    fun en => (pt_str _ _ _).trans (hb b).symm).exists
  refine ⟨P, p0, p, h, ⟨fun b w => (hh b w).1, fun b w en => ⟨_, (hh b w).2 en⟩⟩, hP, hp, fun Z a a' h0 h1 => ?_⟩
  exact (univ Z (a ≫ p0) (fun en => a ≫ p en) fun en => by
    rw [Category.assoc, hp, Category.assoc]).unique ⟨rfl, fun _ => rfl⟩ ⟨h0.symm, fun en => (h1 en).symm⟩

end GlobalTheory.FlagEmb
end

section

open GlobalTheory.ShFam.Hor


theorem _root_.GlobalTheory.T.exists_holomorphic_descent_punctPolydisc_logCover : ∀ (n a : ℕ) (ρ : ℝ) (h : (Fin n → ℂ) → ℂ), 0 < ρ → ρ ≤ 1 → DifferentiableOn ℂ h {s | s ∈ logDom n a ∧ logExp a s ∈ Metric.ball (0 : Fin n → ℂ) ρ} → (∀ s ∈ logDom n a, logExp a s ∈ Metric.ball (0 : Fin n → ℂ) ρ → ∀ k : Fin n, (k : ℕ) < a → h (s + Pi.single k (2 * Real.pi * Complex.I)) = h s) → ∃ H : (Fin n → ℂ) → ℂ, DifferentiableOn ℂ H {z | z ∈ Metric.ball (0 : Fin n → ℂ) ρ ∧ ∀ k : Fin n, (k : ℕ) < a → z k ≠ 0} ∧ ∀ s ∈ logDom n a, logExp a s ∈ Metric.ball (0 : Fin n → ℂ) ρ → h s = H (logExp a s) := by
  first | exact @GlobalTheory.LogDescent.descent | exact GlobalTheory.LogDescent.descent | (intros; apply GlobalTheory.LogDescent.descent <;> assumption)
end
