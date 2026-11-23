module

public import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.DeltaDatumCombinedCoefficient
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle024
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle034
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle031
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle079
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsReducedAlgebraOfSmoothOfIsNoetherianRing
import Formalism.LocalToGlobal.ProjectiveLattices.FrameCharts
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle025
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.CoeSelfDualLatticeInFrameCoordinatesEq
public import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle073
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.NormConst
public import Development.AbelianVarietyTheory.PublishedTheorems.Landherr₂.ExistsNormTensor
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle102
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle030
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle037
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle012
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle187
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle082
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle078
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle093
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle079
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle028
import Formalism.LocalToGlobal.ProjectiveLattices.DatProofs
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle126
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle068
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedModuliAlgebraicLawsChartWeightIntegrality
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedPointReducedFromTestRing
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.TypeFnPeriodExistModuliNonempty
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle027
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
import Mathlib.Tactic.TypeStar

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.IndefiniteRowSideFullHecke.DeltaDatumCombinedCoefficient

namespace GlobalTheory.FrameFreeRule

theorem fnAt_comp {X Y : Scheme.{0}} {S : Type} [CommRing S] (y : Sp S ⟶ X) (g : X ⟶ Y) (f : Γ(Y, ⊤)) :
    fnAt (y ≫ g) f = fnAt y (g.appTop.hom f) := by
  simp only [fnAt, Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply]

theorem fnAt_spMap_comp {X : Scheme.{0}} {S T : Type} [CommRing S] [CommRing T] (φ : S →+* T) (y : Sp S ⟶ X)
    (f : Γ(X, ⊤)) : fnAt (spMap φ ≫ y) f = φ (fnAt y f) := by
  rw [fnAt_comp]
  exact congrArg (fun q => q.hom (y.appTop.hom f)) (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom φ))

theorem fnAt_id {S : Type} [CommRing S] (a : S) :
    fnAt (𝟙 (Sp S)) ((Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom a) = a := by
  simp [fnAt]

theorem eq_zero_of_geometric {P : Scheme.{0}} [IsReduced P] (s : Γ(P, ⊤))
    (h : ∀ (K : Type) [Field K] [IsAlgClosed K] (y : Sp K ⟶ P), fnAt y s = 0) : s = 0 := by
  rw [← basicOpen_eq_bot_iff, eq_bot_iff]
  intro x hx
  let K := AlgebraicClosure (P.residueField x)
  let y : Sp K ⟶ P := spMap (algebraMap (P.residueField x) K) ≫ P.fromSpecResidueField x
  have h0 : y.appTop.hom s = 0 := by
    have := h K y
    unfold fnAt at this
    exact (map_eq_zero_iff _ (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv.injective).1 this
  have h1 : y ⁻¹ᵁ P.basicOpen s = ⊥ := by
    rw [Scheme.preimage_basicOpen_top]
    erw [h0]
    exact Scheme.basicOpen_zero _ _
  have h2 : (default : Sp K) ∈ y ⁻¹ᵁ P.basicOpen s := by
    change y default ∈ P.basicOpen s
    have : y default = x := by
      simp only [y, Scheme.Hom.comp_apply]
      exact Scheme.fromSpecResidueField_apply _ _
    rwa [this]
  rw [h1] at h2
  exact h2

theorem hom_ext_of_geometric {P Y : Scheme.{0}} [IsReduced P] [IsAffine Y] (u v : P ⟶ Y)
    (h : ∀ (K : Type) [Field K] [IsAlgClosed K] (y : Sp K ⟶ P), y ≫ u = y ≫ v) : u = v := by
  refine ext_of_isAffine ?_
  ext r
  rw [← sub_eq_zero]
  refine eq_zero_of_geometric _ fun K _ _ y => ?_
  have := congrArg (fun q => fnAt q r) (h K y)
  simp only [fnAt_comp] at this
  unfold fnAt at this ⊢
  rw [map_sub, map_sub, sub_eq_zero]
  exact this

theorem exists_glue {X : Scheme.{0}} [IsReduced X] {ι : Type} (A : ι → Type) [∀ i, CommRing (A i)]
    (j : ∀ i, Sp (A i) ⟶ X) [∀ i, IsOpenImmersion (j i)] (hcov : ∀ x : X, ∃ i, x ∈ Set.range (j i))
    (a : ∀ i, A i)
    (h : ∀ (K : Type) [Field K] [IsAlgClosed K] (i i' : ι) (χ : A i →+* K) (χ' : A i' →+* K),
      spMap χ ≫ j i = spMap χ' ≫ j i' → χ (a i) = χ' (a i')) :
    ∃ f : Γ(X, ⊤), ∀ i, fnAt (j i) f = a i := by
  let 𝒰 : X.OpenCover := Scheme.Cover.mkOfCovers ι (fun i => Sp (A i)) j
    (fun x => by obtain ⟨i, y, hy⟩ := hcov x; exact ⟨i, y, hy⟩)
  let ev : ∀ i, Polynomial ℤ →+* A i := fun i => Polynomial.eval₂RingHom (Int.castRingHom _) (a i)
  let g : ∀ i, Sp (A i) ⟶ Sp (Polynomial ℤ) := fun i => spMap (ev i)
  have hg : ∀ i i', pullback.fst (j i) (j i') ≫ g i = pullback.snd (j i) (j i') ≫ g i' := by
    intro i i'
    have : IsReduced (pullback (j i) (j i')) :=
      isReduced_of_isOpenImmersion (pullback.fst (j i) (j i') ≫ j i)
    refine hom_ext_of_geometric _ _ fun K _ _ y => ?_
    obtain ⟨χ, hχ⟩ := Spec.map_surjective (y ≫ pullback.fst (j i) (j i'))
    obtain ⟨χ', hχ'⟩ := Spec.map_surjective (y ≫ pullback.snd (j i) (j i'))
    have e := h K i i' χ.hom χ'.hom (by
      change Spec.map χ ≫ _ = Spec.map χ' ≫ _
      rw [hχ, hχ', Category.assoc, Category.assoc, pullback.condition])
    rw [← Category.assoc, ← Category.assoc, ← hχ, ← hχ']
    change spMap χ.hom ≫ spMap (ev i) = spMap χ'.hom ≫ spMap (ev i')
    rw [GlobalTheory.LocalFrame.spMap_spMap, GlobalTheory.LocalFrame.spMap_spMap]
    congr 1
    refine Polynomial.ringHom_ext (fun n => by simp) ?_
    simpa [ev] using e
  let G : X ⟶ Sp (Polynomial ℤ) := 𝒰.glueMorphisms g hg
  refine ⟨G.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of (Polynomial ℤ))).inv.hom Polynomial.X), fun i => ?_⟩
  have hi : j i ≫ G = g i := 𝒰.ι_glueMorphisms g hg i
  rw [← fnAt_comp, hi, ← Category.comp_id (g i), fnAt_spMap_comp, fnAt_id]
  simp [ev]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l}

theorem evR_eq_of_chart (s : Rul Xo c) (hs : s ∈ sec Xo c 0 0)
    (hfree : ∀ (K : Type) [Field K] [IsAlgClosed K] [Algebra c.F K] (y y' : FrPt Xo c K),
      y'.x = y.x → evR Xo c s y' = evR Xo c s y)
    {A : Type} [CommRing A] [IsDomain A] [Algebra c.F A] (u : FrPt Xo c A)
    {K : Type} [Field K] [IsAlgClosed K] [Algebra c.F K] (χ : A →ₐ[c.F] K) (y : FrPt Xo c K)
    (hy : y.x = spMap χ.toRingHom ≫ u.x) : evR Xo c s y = χ (evR Xo c s u) := by
  obtain ⟨z, hz⟩ := GlobalTheory.TransferCompare.frBC_framed Xo c A K χ u
  rw [hfree K z y (hy.trans hz.1.symm)]
  have hT1 := GlobalTheory.TransferCompare.allTest_framed Xo c A u
  have hT2 := GlobalTheory.TransferCompare.allTest_framed Xo c K z
  unfold evR evalAt
  rw [dite_eq_left hT2, dite_eq_left hT1]
  exact GlobalTheory.TransferCompare.evalWD_framed Xo c s hs.1 K _ _ _ _ _ _ z hT2.choose_spec.choose_spec.choose_spec
    (frMap_trans (Xo := Xo) (c := c) _ _ _ _ χ _ u z hT1.choose_spec.choose_spec.choose_spec hz)

theorem exists_fn : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (s : Rul Xo c), s ∈ sec Xo c 0 0 → (∀ (K : Type) [Field K] [IsAlgClosed K] [Algebra c.F K] (y y' : FrPt Xo c K), y'.x = y.x → evR Xo c s y' = evR Xo c s y) → ∃ f : Γ(Xo.XF c, ⊤), ∀ (K : Type) [Field K] [IsAlgClosed K] [Algebra c.F K] (y : FrPt Xo c K), evR Xo c s y = GlobalTheory.IndefiniteRowSideFullHecke.DeltaDatumCombinedCoefficient.fnAt (GlobalTheory.IndefiniteRowSideFullHecke.DeltaDatumCombinedCoefficient.basePt y) f := by
  intro E _ _ _ H D l Xo c s hs hfree
  choose A iA dA aA j u hj hp hsn _ hu using
    GlobalTheory.LocalFrame.exists_integral_chart_frame GlobalTheory.abelianSchemeLaws_all.2.secTwist E H D l Xo c
  have := Xo.smooth
  have : Smooth Xo.s := SmoothOfRelativeDimension.smooth D.dim Xo.s
  have : IsReduced (Xo.XF c) := GlobalTheory.isReduced_of_smooth_of_isReduced (pullback.snd _ _)
  have key : ∀ (K : Type) [Field K] [IsAlgClosed K] [Algebra c.F K] (y : FrPt Xo c K) (p : Xo.XF c) (χ : A p →+* K),
      spMap χ ≫ j p = basePt y → evR Xo c s y = χ (evR Xo c s (u p)) := by
    intro K _ _ _ y p χ hχ
    have h1 : χ.comp (algebraMap c.F (A p)) = algebraMap c.F K := by
      have h2 : spMap (χ.comp (algebraMap c.F (A p))) = spMap (algebraMap c.F K) := by
        rw [← GlobalTheory.LocalFrame.spMap_spMap, ← hsn, ← Category.assoc, hχ]
        exact pullback.lift_snd _ _ _
      exact congrArg CommRingCat.Hom.hom (Spec.map_injective h2)
    refine evR_eq_of_chart s hs hfree (u p) ⟨χ, fun r => RingHom.congr_fun h1 r⟩ y ?_
    change y.x = spMap χ ≫ _
    rw [hu, ← Category.assoc, hχ]
    exact (pullback.lift_fst _ _ _).symm
  obtain ⟨f, hf⟩ := exists_glue A j (fun x => ⟨x, hp x⟩) (fun p => evR Xo c s (u p)) (by
    intro K _ _ p p' χ χ' hχ
    letI : Algebra c.F K := (χ.comp (algebraMap c.F (A p))).toAlgebra
    have hsn' : (spMap χ ≫ j p) ≫ pullback.snd _ _ = spMap (algebraMap c.F K) := by
      rw [Category.assoc, hsn, GlobalTheory.LocalFrame.spMap_spMap]
    have hx : ((spMap χ ≫ j p) ≫ pullback.fst _ _) ≫ Xo.s = sOf c K := by
      rw [Category.assoc, pullback.condition, ← Category.assoc, hsn', sOf, GlobalTheory.LocalFrame.spMap_spMap]
    obtain ⟨y, hy⟩ : ∃ y : FrPt Xo c K, y.x = (spMap χ ≫ j p) ≫ pullback.fst _ _ := by
      choose u hu using fun τ => GlobalTheory.IntFramesCompare.exists_eigenBasisAt (c := c) hx τ
      obtain ⟨s, hs⟩ := gfp_gen GlobalTheory.abelianSchemeLaws_all.2.secTwist ((spMap χ ≫ j p) ≫ pullback.fst _ _)
      exact ⟨⟨_, hx, u, fun τ => (hu τ).1, fun τ => (hu τ).2.1, fun τ => (hu τ).2.2, s, hs⟩, rfl⟩
    have hb : spMap χ ≫ j p = basePt y := by
      refine pullback.hom_ext ?_ ?_
      · rw [← hy]; exact (pullback.lift_fst _ _ _).symm
      · rw [hsn']; exact (pullback.lift_snd _ _ _).symm
    exact (key K y p χ hb).symm.trans (key K y p' χ' (hχ.symm.trans hb)))
  refine ⟨f, fun K _ _ _ y => ?_⟩
  let p : Xo.XF c := basePt y default
  have hr : Set.range (basePt y) ⊆ Set.range (j p) := by
    rintro _ ⟨q, rfl⟩
    rw [Subsingleton.elim q default]
    exact hp p
  obtain ⟨χ, hχ⟩ := Spec.map_surjective (IsOpenImmersion.lift (j p) (basePt y) hr)
  have hb : spMap χ.hom ≫ j p = basePt y := by
    change Spec.map χ ≫ _ = _
    rw [hχ, IsOpenImmersion.lift_fac]
  rw [key K y p χ.hom hb, ← hb, fnAt_spMap_comp, hf]

end GlobalTheory.FrameFreeRule
end

section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Member

namespace GlobalTheory.Member

theorem hostCMType_neg_constant_im_neg (D : D7) (τ : D.host.E →+* ℂ)
    (hτ : τ D.host.sqrtMinusD = D.host.φ₀ D.host.sqrtMinusD) : (τ (-D.host.xi0)).im < 0 := by
  have h1 := xi0_embedding_im_pos D τ ((mem_cm_type_iff D τ).2 hτ)
  have hφ : D.host.φ₀ D.host.sqrtMinusD = Complex.I * (Real.sqrt D.host.d : ℂ) := D.host.φ₀_mem
  have hpos : 0 < (D.host.φ₀ D.host.sqrtMinusD).im := by
    rw [hφ]
    have hd : (0 : ℝ) < D.host.d := by exact_mod_cast d_pos D
    simpa using hd
  rw [if_pos hpos, Int.cast_one, _root_.one_mul] at h1
  rw [map_neg, Complex.neg_im]
  linarith

theorem exists_family_models (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (V : HSp D)
    (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)) (hι : IotaOK Dw V ι) (hpos : 1 ≤ Dw.p + Dw.q)
    (hσ : GoodEmb c σ) :
    ∃ (g : ℕ) (e : Fin g ≃ Σ τ : D.host.E →+* ℂ, Fin (Dw.mult τ))
      (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1))
      (M : GlobalTheory.FrameUnif.ModelsOf F V.rank), GlobalTheory.FrameUnif.ModelBase M ∧ ∀ k, ModelW V rfl (M.X k) := by
  classical
  let e := (Fintype.equivFin (Σ τ : D.host.E →+* ℂ, Fin (Dw.mult τ))).symm
  have hty := (GlobalTheory.Relab.relab_good D.host.E H l c σ hσ).2.2.2 Dw _ e
  obtain ⟨F⟩ := GlobalTheory.closing_of_abelianSchemeLaws D.host.E H Dw l Xo
    (σ.comp (IntermediateField.inclusion c.le).toRingHom) _ (fun j => relab c σ (e j).1) hpos hσ hty
  obtain ⟨-, -, -, -, -, hcF, -, hherm, hdet, hhT, -⟩ := GlobalTheory.Member.latHat_eq_hat_and_gram D V
  have hξ : cc (-D.host.xi0) = -(-D.host.xi0) := by rw [cc, map_neg, conj_xi0_alt]
  have hsp : Submodule.span D.host.E (Set.range ι) = ⊤ := by
    rw [← LinearMap.coe_range, hι.emb.2]
    exact (GlobalTheory.Member.latG_lattice_and_completion D V 1).2.1
  have hG : ∀ a b, cc ((-V.gramᵀ) a b) = (-V.gramᵀ) b a := fun a b => by
    rw [Matrix.neg_apply, Matrix.neg_apply, cc, map_neg, ← hherm a b, hcF, cc]
  have hd : (-V.gramᵀ).det ≠ 0 := by
    rw [Matrix.det_neg]
    exact mul_ne_zero (pow_ne_zero _ (by simp)) hdet
  have hEF : ∀ x y, ((Dw.EF x y : ℤ) : ℚ) =
      Algebra.trace ℚ D.host.E (-(-D.host.xi0) * herm (-V.gramᵀ) (ι x) (ι y)) := fun x y => by
    have h1 : Dw.EF x y = -Dw.EF y x := by
      have h := Dw.alt (x + y)
      simp only [map_add (f := _), LinearMap.add_apply, Dw.alt] at h
      linarith
    rw [h1, Int.cast_neg, hι.isom y x, hhT, ← map_neg]
    congr 1
    ring
  obtain ⟨M, hM, -, hMG⟩ := GlobalTheory.ModelsExist.exists_modelsOf GlobalTheory.QNorm.hasseNormSt D.host.E H Dw l Xo _ _ _ F
    V.rank (-D.host.xi0) (-V.gramᵀ) ι hξ
    (fun τ hτ => hostCMType_neg_constant_im_neg D τ (by rw [← hι.rt0, ← hι.rt, hτ])) ⟨hι.emb.1, hsp, hG, hd, hEF⟩
  exact ⟨_, e, F, M, hM, fun k => ⟨(hMG k).1, (hMG k).2⟩⟩

theorem exists_ctx : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (V : HSp D) (r : ℕ) (hr : V.rank = r) (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)), IotaOK Dw V ι → 1 ≤ Dw.p + Dw.q → l.A = 1 → GoodEmb c σ → (∃ C : Ctx Xo c σ V r, C.OK ∧ C.ι = ι) ∧ (∀ C : Ctx Xo c σ V r, C.OK → GlobalTheory.FrameUnif.NegXi C.M) ∧ ∀ x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ, (∀ τ : D.host.E →+* ℂ, τ (H.rt : D.host.E) = H.rt0 → gram τ (-(Matrix.reindex (finCongr hr) (finCongr hr) V.gram)ᵀ) (x₀ τ) = Matrix.diagonal fun a : Fin r => ((sgn Dw.q (a : ℕ) : ℝ) : ℂ)) → ∃ C : Ctx Xo c σ V r, C.OK ∧ C.ι = ι ∧ C.x₀ = x₀ := by
  intro D H Dw l Xo c σ V r hr ι hι hpos hA hσ
  subst hr
  obtain ⟨g, e, F, M, hM, hW⟩ := exists_family_models D H Dw l Xo c σ V ι hι hpos hσ
  obtain ⟨θ, hθ⟩ := (GlobalTheory.Member.infiniteAdele_bijective D).1
  have key : ∀ x₀ : (D.host.E →+* ℂ) → Matrix (Fin V.rank) (Fin V.rank) ℂ,
      (∀ τ : D.host.E →+* ℂ, τ (H.rt : D.host.E) = H.rt0 →
        gram τ (-(Matrix.reindex (finCongr rfl) (finCongr rfl) V.gram)ᵀ) (x₀ τ) =
          Matrix.diagonal fun a : Fin V.rank => ((sgn Dw.q (a : ℕ) : ℝ) : ℂ)) →
      ∃ C : Ctx Xo c σ V V.rank, C.OK ∧ C.ι = ι ∧ C.x₀ = x₀ := fun x₀ hx =>
    ⟨⟨rfl, g, e, F, M, ι, θ, x₀⟩, ⟨hι, hpos, hA, hσ, hM, hW, hθ, fun k τ hτ => by
      show gram τ (M.X k).Gm (x₀ τ) = Matrix.diagonal fun a : Fin V.rank => ((sgn (M.X k).p0 (a : ℕ) : ℝ) : ℂ)
      rw [(hW k).1, (hM.type k).1]
      exact hx τ (((hM.type k).2 τ).1 hτ)⟩, rfl, rfl⟩
  refine ⟨?_, fun C hC k τ hτ => ?_, key⟩
  · classical
    let k : Fin F.n := ⟨0, F.n_pos⟩
    obtain ⟨C, hC, h, -⟩ := key
      (fun τ => if h : τ ∈ (M.X k).Ψ then ((M.X k).signature ⟨τ, h⟩).choose else 1) fun τ hτ => by
        have h := ((hM.type k).2 τ).2 hτ
        rw [dite_eq_left h, ← (hW k).1, ← (hM.type k).1]
        exact ((M.X k).signature ⟨τ, h⟩).choose_spec.2
    exact ⟨C, hC, h⟩
  · rw [(hC.modelW k).2]
    exact hostCMType_neg_constant_im_neg D τ (by rw [← hι.rt0, ← hι.rt, ((hC.base.type k).2 τ).1 hτ])

end GlobalTheory.Member
end

section

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors

theorem GlobalTheory.selfDual_lattice_occurs : GlobalTheory.Published.HasseNormSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (σ' : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (F : FamilyUnif Xo σ' ty) (r : ℕ) (M : _root_.GlobalTheory.FrameUnif.ModelsOf F r) (ξ₀ : E) (Gm : Matrix (Fin r) (Fin r) E) (φ : Dw.La →ₗ[𝓞 E] (Fin r → E)) (Λ' : Submodule (𝓞 E) (Fin r → E)) (f : ℕ → Dw.La →ₗ[𝓞 E] Λ'), l.A = 1 → σ' (baseKA l).ρ = H.rt0 → IsTypeFn H Dw.p Dw.q ty → ModelBase M → (∀ k, (M.X k).Gm = Gm ∧ (M.X k).ξ0 = ξ₀) → (Function.Injective φ ∧ Submodule.span E (Set.range φ) = ⊤ ∧ (∀ a b, cc (Gm a b) = Gm b a) ∧ Gm.det ≠ 0 ∧ ∀ x y, ((Dw.EF x y : ℤ) : ℚ) = Algebra.trace ℚ E (-ξ₀ * herm Gm (φ x) (φ y))) → Λ'.FG → Submodule.span E (Λ' : Set (Fin r → E)) = ⊤ → (∀ v : Fin r → E, (∀ y ∈ Λ', ∃ n : ℤ, Algebra.trace ℚ E (-ξ₀ * herm Gm v y) = n) ↔ v ∈ Λ') → (∀ n m : ℕ, 0 < n → 0 < m → ∀ a, ∃ v, f (n * m) a = f n a + n • v) → (∀ n : ℕ, 0 < n → (∀ a, (∃ v, f n a = n • v) ↔ ∃ v, a = n • v) ∧ ∀ a', ∃ a v, a' = f n a + n • v) → (∀ n : ℕ, 0 < n → ∀ a a', ∃ z : ℤ, Algebra.trace ℚ E (-ξ₀ * herm Gm (f n a) (f n a')) - (Dw.EF a a' : ℤ) = n * z) → ∃ (k : Fin F.n) (γ : GL (Fin r) E), (∀ u v, herm Gm ((γ : Matrix (Fin r) (Fin r) E) *ᵥ u) ((γ : Matrix (Fin r) (Fin r) E) *ᵥ v) = herm Gm u v) ∧ (∀ v, v ∈ Λ' ↔ (γ : Matrix (Fin r) (Fin r) E) *ᵥ v ∈ (M.X k).Λ) ∧ ∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) Dw.La), ∃ w ∈ (M.X k).Λ, (γ : Matrix (Fin r) (Fin r) E) *ᵥ (f l.M a : Fin r → E) = (M.φ k (F.t k a) : Fin r → E) + l.M • w := by
  intro hH E _ _ _ H Dw l Xo σ' g ty F r M ξ₀ Gm φ Λ' f hA hσ hty hM hk hφ hfg hsp hsd hc hb hi
  have hξ : cc (-ξ₀) = -(-ξ₀) := by
    have h := (M.X ⟨0, F.n_pos⟩).ξ0_im
    rw [(hk _).2] at h
    unfold cc at h ⊢
    rw [map_neg, h]
  obtain ⟨D', φ', hp, hq, hr, hφ'⟩ := GlobalTheory.T.exists_latticeDatum_of_selfDual_lattice E H Dw r (-ξ₀) Gm φ Λ' hξ hφ hfg hsp hsd
  let e : D'.La ≃ₗ[𝓞 E] Λ' := (LinearEquiv.ofInjective φ' hφ'.1).trans (LinearEquiv.ofEq _ _ hr)
  have he : ∀ x, φ' (e.symm x) = (x : Fin r → E) := fun x => by
    have : ∀ y, ((e y : Λ') : Fin r → E) = φ' y := fun y => rfl
    rw [← this, e.apply_symm_apply]
  obtain ⟨k, gam, hg1, hg2⟩ := GlobalTheory.allClassesSt_of_hasseNorm hH E H Dw l Xo σ' g ty F hA hσ hty D'
    (fun n => e.symm.toLinearMap ∘ₗ f n) hp hq
    ⟨fun n m hn hm a => by
      obtain ⟨v, hv⟩ := hc n m hn hm a
      exact ⟨e.symm v, by simp [hv]⟩,
     fun n hn => ⟨fun a => by
      rw [← (hb n hn).1 a]
      constructor
      · rintro ⟨v, hv⟩
        refine ⟨e v, ?_⟩
        rw [← map_nsmul, ← hv]
        simp
      · rintro ⟨v, hv⟩
        exact ⟨e.symm v, by simp [hv]⟩,
      fun a' => by
        obtain ⟨a, v, hv⟩ := (hb n hn).2 (e a')
        refine ⟨a, e.symm v, ?_⟩
        apply e.injective
        simp [hv]⟩⟩
    (fun n hn a a' => by
      obtain ⟨z, hz⟩ := hi n hn a a'
      refine ⟨z, ?_⟩
      have h := hφ'.2.2.2.2 (e.symm (f n a)) (e.symm (f n a'))
      rw [he, he] at h
      rw [← h] at hz
      exact_mod_cast hz)
  let ψ : (F.Di k).La →ₗ[𝓞 E] (Fin r → E) := (M.X k).Λ.subtype ∘ₗ (M.φ k).toLinearMap
  have hψ : ∀ a, ψ a = (M.φ k a : Fin r → E) := fun a => rfl
  have hrange : Set.range ψ = ((M.X k).Λ : Set (Fin r → E)) := by
    ext v
    constructor
    · rintro ⟨a, rfl⟩
      exact (M.φ k a).2
    · intro hv
      exact ⟨(M.φ k).symm ⟨v, hv⟩, by rw [hψ, LinearEquiv.apply_symm_apply]⟩
  obtain ⟨γ, hγ1, hγ2⟩ := GlobalTheory.T.exists_unitary_matrix_of_lattice_isometry E H D' (F.Di k) r (-ξ₀) Gm φ' ψ gam hξ hφ'
    ⟨Subtype.val_injective.comp (M.φ k).injective, by rw [hrange]; exact (M.X k).Λ_span, hφ.2.2.1, hφ.2.2.2.1,
      fun x y => by
        have h := hM.ef k x y
        rw [(hk k).1, (hk k).2] at h
        exact h⟩ hg1
  refine ⟨k, γ, hγ1, fun v => ⟨fun hv => ?_, fun hv => ?_⟩, fun a ha => ?_⟩
  · have h := hγ2 (e.symm ⟨v, hv⟩)
    rw [he] at h
    rw [← h]
    exact (M.φ k _).2
  · have h := hγ2 (gam.symm ((M.φ k).symm ⟨_, hv⟩))
    rw [LinearEquiv.apply_symm_apply, hψ, LinearEquiv.apply_symm_apply] at h
    have h2 := congrArg (fun w => ((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ w) h
    simp only [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec] at h2
    rw [h2, ← hr]
    exact LinearMap.mem_range_self _ _
  · obtain ⟨w, hw⟩ := hg2 a ha
    refine ⟨M.φ k w, (M.φ k w).2, ?_⟩
    have h := hγ2 (e.symm (f l.M a))
    rw [he] at h
    rw [← h]
    change ψ (gam ((e.symm.toLinearMap ∘ₗ f l.M) a)) = ψ (F.t k a) + l.M • ψ w
    rw [hw, map_add (f := _), map_nsmul]
end

section

namespace GlobalTheory.Reg

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain in
private theorem nonempty_irreducibleComponents_of_point {X : Type*} [TopologicalSpace X] (x : X) :
    Nonempty (irreducibleComponents X) :=
  ⟨⟨irreducibleComponent x, irreducibleComponent_mem_irreducibleComponents x⟩⟩


open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain in
theorem _root_.GlobalTheory.Reg.evLaws_genFr_nonempty_comp : ∀ (E : Type) [Field E] [NumberField E]
    [IsCMField E] (H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H) (l : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l)
    (c : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l), _root_.GlobalTheory.Reg.EvLaws Xo c ∧ _root_.Formalism.L2.Pj.IntDiagUnit Xo c ∧ _root_.Formalism.L2.Pj.GenFrEx Xo c ∧
      (1 ≤ Dw.p + Dw.q → Nonempty (_root_.Formalism.L2.Pj.Comp Xo c)) := by
  intro E _ _ _ H Dw l Xo c
  have hsec : _root_.ReciprocityTheory.ChartRestriction.G.Out.SecBaseChangeSt := _root_.GlobalTheory.allSixLaws.1.secBaseChange
  have htw : _root_.ReciprocityTheory.ChartRestriction.G.Out.SecTwistSt := _root_.GlobalTheory.allSixLaws.2.1.secTwist
  obtain ⟨-, -, hwd, hwt, hdiag, -, -⟩ :=
    _root_.GlobalTheory.Frames.algebraic_laws hsec E H Dw l Xo c
  refine ⟨⟨hwd, _root_.GlobalTheory.Frames.allTest_of_secBaseChange hsec E H Dw l Xo c, hwt, ?_⟩, hdiag,
    _root_.Formalism.L2.Pj.genFrEx_of htw, ?_⟩
  · intro S T _ _ _ _ φ y
    exact _root_.GlobalTheory.Frames.FramedBaseChange.exists_frMap hsec E H Dw l Xo c S T φ y
  · intro hpq
    obtain ⟨x⟩ := (_root_.GlobalTheory.PeriodExists.typeFn_period_exist E H Dw).2.2
      _root_.GlobalTheory.closing_of_abelianSchemeLaws hpq l Xo c
    unfold _root_.Formalism.L2.Pj.Comp
    exact nonempty_irreducibleComponents_of_point x

end GlobalTheory.Reg
end
