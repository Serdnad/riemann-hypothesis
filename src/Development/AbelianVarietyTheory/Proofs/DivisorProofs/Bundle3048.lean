module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2589
public import Development.AbelianVarietyTheory.Definitions.Divisors.BarCompSubsetClosure
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle411
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2659
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2607
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2609
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2660
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2658
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2950
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2606
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.BijectiveAlgebraMapIntegralClosureOfBirational
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle651
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle534
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle711
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2662
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2672
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2954
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2832
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2951
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle357
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsTorusAndQuotientHom
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle147
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2666
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle532
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle051
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2636
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle681
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2744
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalSymplecticSimilitudeClassifyingMaps
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Basify
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle007
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbelianSchemeGerms
import Mathlib.Tactic.Polynomial.Basic
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle067
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUnifOfIsMumfordOf
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle074
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle012

@[expose] public section

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.VarFlag
open GlobalTheory.FlagMod (FlagCover FlagModel Frames)
open GlobalTheory.ShFam (EigFrame FlagCpt)
open ReciprocityTheory.AnForm.R.FinalTheorems (Snc)
open GlobalTheory.Toroidal (gen genι genStr genBd genBdIdeal)
open GlobalTheory.CompHS (Y₀ inc₀ str₀ barComp U₀ IsVariety₀ TorFlag dense_U₀ flagStr flagOpen)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)}

theorem Rel.over (X : FlagCover Y) (C : FlagCpt Y (RingEquiv.refl c.F)) {K : Type} [Field K] {z : Sp K ⟶ X.YY} {p : Sp K ⟶ C.Y.X}
    (h : Rel X.F C z p) : z ≫ X.π = p ≫ C.π ≫ genι Y := by
  obtain ⟨φ, k, hz, g, -, -, y, ψ, φ₁, f, t, t', hp, -, hT⟩ := h
  rw [hT.1, hp]
  simp only [Category.assoc]

theorem barComp_iff (Z : Formalism.L2.Pj.Comp Xo c) (B : Formalism.L2.Pj.Comp Xo c → GlobalTheory.ProjVar.Var c.F) (j : ∀ i, (B i).X ⟶ gen Y)
    (h1 : ∀ i, IsOpenImmersion (j i)) (h2 : ∀ i, ∀ p ∈ i.1, Y.jQ p ∈ Set.range (j i))
    (h3 : ∀ z : gen Y, ∃! i, z ∈ Set.range (j i)) (w : gen Y) :
    genι Y w ∈ barComp Y Z ↔ w ∈ Set.range (j Z) := by
  have hY : ∀ p : Xo.XF c, Y.j p = genι Y (Y.jQ p) := fun p => rfl
  have hc : ∀ p : Xo.XF c, ∃ i : Formalism.L2.Pj.Comp Xo c, p ∈ i.1 := fun p => by
    obtain ⟨u, hu, hs⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible _ (isIrreducible_singleton (x := p))
    exact ⟨⟨u, hu⟩, hs rfl⟩
  have key : ∀ p : Xo.XF c, Y.jQ p ∈ Set.range (j Z) → p ∈ Z.1 := fun p hp => by
    obtain ⟨i, hi⟩ := hc p
    obtain ⟨i', -, hu'⟩ := h3 (Y.jQ p)
    have e : i = Z := (hu' i (h2 i p hi)).trans (hu' Z hp).symm
    exact e ▸ hi
  obtain ⟨i, hi, -⟩ := h3 w
  constructor
  · intro hw
    by_contra hn
    have hiZ : i ≠ Z := fun e => hn (e ▸ hi)
    apply hw
    rw [mem_closure_iff]
    intro O hO hwO
    have := h1 i
    obtain ⟨_, hp, ⟨p, rfl⟩⟩ := Y.jQ_dense.inter_open_nonempty _
      ((hO.preimage (genι Y).continuous).inter (j i).isOpenEmbedding.isOpen_range) ⟨w, hwO, hi⟩
    refine ⟨Y.j p, hp.1, p, fun hpZ => ?_, rfl⟩
    obtain ⟨i', -, hu'⟩ := h3 (Y.jQ p)
    exact hiZ ((hu' i hp.2).trans (hu' Z (h2 Z p hpZ)).symm)
  · rintro ⟨b, rfl⟩ hw
    have := h1 Z
    rw [mem_closure_iff] at hw
    obtain ⟨_, ⟨w', hw', he⟩, ⟨p, hpZ, hp⟩⟩ := hw (genι Y '' Set.range (j Z))
      ((genι Y).isOpenEmbedding.isOpenMap _ (j Z).isOpenEmbedding.isOpen_range) ⟨_, ⟨b, rfl⟩, rfl⟩
    have e : w' = Y.jQ p := (genι Y).isOpenEmbedding.injective (he.trans (hp.symm.trans (hY p)))
    exact hpZ (key p (e ▸ hw'))

theorem genStr_eq : genStr Y = genι Y ≫ Y.s := by
  have h : spMap (RingHom.id c.F) = 𝟙 _ := Spec.map_id _
  exact ((Category.comp_id _).symm.trans (congrArg (genStr Y ≫ ·) h.symm)).trans pullback.condition.symm

theorem smooth_iso {A B S : Scheme.{0}} (e : A ⟶ B) [IsIso e] (g : B ⟶ S) {d : ℕ} (h : SmoothOfRelativeDimension d g) :
    SmoothOfRelativeDimension d (e ≫ g) := by
  have := smoothOfRelativeDimension_comp 0 d e g
  rwa [Nat.zero_add] at this

theorem smooth_gen {d : ℕ} (h : SmoothOfRelativeDimension d Y.s) : SmoothOfRelativeDimension d (genStr Y) := by
  rw [genStr_eq]
  exact smooth_iso _ _ h

theorem isVariety_of_iso (X : FlagCover Y) (Z : Formalism.L2.Pj.Comp Xo c) (C : FlagCpt Y (RingEquiv.refl c.F))
    (e : Y₀ X Z ⟶ C.Y.X) [IsIso e] (he : e ≫ C.Y.str = str₀ X Z) (hd : C.Y.dim = GlobalTheory.FlagTan.dimFlag Dw) : IsVariety₀ X Z := by
  refine ⟨?_, ?_, ?_⟩
  · rw [← he, ← hd]
    exact smooth_iso _ _ inferInstance
  · obtain ⟨N, i, hi, hs⟩ := C.Y.isProjOver
    exact ⟨N, e ≫ i, inferInstance, by rw [Category.assoc, hs, he]⟩
  · rw [← he]
    exact MorphismProperty.of_isPullback (P := @GeometricallyConnected)
      (IsPullback.of_horiz_isIso ⟨by simp⟩ : IsPullback e (e ≫ C.Y.str) C.Y.str (𝟙 _)) inferInstance

theorem dim_eq (Dw : Datum H) : Dw.dim + ∑ τ : E →+* ℂ, (Dw.mult τ).choose 2 = GlobalTheory.FlagTan.dimFlag Dw := by
  rw [GlobalTheory.FlagDimSum.dim_add_sum_choose, GlobalTheory.FlagTan.dimFlag, Nat.choose_two_right]

theorem isVariety₀_flag : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (T : TorFlag Xo c) (Z : Comp Xo c), FnAlgClosed (Xo := Xo) (c := c) → IsVariety₀ T.X Z := by
  intro E _ _ _ H Dw l Xo c T Z hF
  have hsm := smooth_gen T.smooth
  obtain ⟨B, j, hB, hcov⟩ := GlobalTheory.T.exists_varieties_components_smooth_genericFibre E H Dw l Xo c c.F (RingHom.id c.F) T.Y c.F (RingEquiv.refl _) hF hsm
  have := (hB Z).1
  obtain ⟨C, f, hπ, hdim, hl⟩ := GlobalTheory.FlagBundle.exists_flagCpt T.Y (RingEquiv.refl _) (GlobalTheory.T.snc_toroidalGenericBoundary_of_snc_boundary T.snc) (B Z) (j Z) (hB Z).2.2.1
  have hJ : ∀ w : gen T.Y, genι T.Y w ∈ barComp T.Y Z ↔ w ∈ Set.range (j Z) :=
    barComp_iff Z B j (fun i => (hB i).1) (fun i => (hB i).2.2.2) hcov
  have hX := GlobalTheory.T.flagChartFrames_eigenFrames_localRing T.X
  have hC := GlobalTheory.T.flagBundlePointFramesTriangular_component C

  have hspid : spMap (RingEquiv.refl c.F).toRingHom = 𝟙 _ := Spec.map_id _
  have hCs : C.π ≫ genStr T.Y = C.Y.str := by
    have := C.π_str
    rwa [hspid, Category.comp_id] at this
  have hps : (C.π ≫ genι T.Y) ≫ T.Y.s = C.Y.str := by rw [Category.assoc, ← genStr_eq, hCs]
  have : IsProper T.Y.s := projProper _ _ _ T.Y.proj
  have : IsProper ((C.π ≫ genι T.Y) ≫ T.Y.s) := by rw [hps]; infer_instance
  have : IsProper (C.π ≫ genι T.Y) := IsProper.of_comp _ T.Y.s

  have hcl : IsClosed (barComp T.Y Z : Set T.Y.X) := by
    rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
    intro y hy
    obtain ⟨w, rfl⟩ : ∃ w, genι T.Y w = y :=
      ⟨inv (genι T.Y) y, by rw [← Scheme.Hom.comp_apply, IsIso.inv_hom_id]; rfl⟩
    obtain ⟨i, hi, -⟩ := hcov w
    have := (hB i).1
    refine ⟨genι T.Y '' Set.range (j i), ?_, ?_, ⟨w, hi, rfl⟩⟩
    · rintro _ ⟨w', hw', rfl⟩ hb
      obtain ⟨i', -, hu'⟩ := hcov w'
      have e : i = Z := (hu' i hw').trans (hu' Z ((hJ w').1 hb)).symm
      subst e
      exact hy ((hJ w).2 hi)
    · exact (genι T.Y).isOpenEmbedding.isOpenMap _ (j i).isOpenEmbedding.isOpen_range
  have : IsClosedImmersion (inc₀ T.X Z) := IsClosedImmersion.of_isPreimmersion _ (by
    rw [Scheme.Opens.range_ι]
    exact hcl.preimage T.X.π.continuous)
  have : IsProper T.X.π := T.X.proper
  have : IsNormalScheme T.X.YY := GlobalTheory.IsNormalScheme.of_pred T.X.normal
  have : IsLocallyNoetherian T.X.YY := LocallyOfFiniteType.isLocallyNoetherian (T.X.π ≫ T.Y.s)
  have : CompactSpace T.Y.X := QuasiCompact.compactSpace_of_compactSpace T.Y.s
  have : CompactSpace T.X.YY := QuasiCompact.compactSpace_of_compactSpace T.X.π
  have : CompactSpace (Y₀ T.X Z) := QuasiCompact.compactSpace_of_compactSpace (inc₀ T.X Z)
  have : IsNoetherian (Y₀ T.X Z) := {}
  have hU : ∀ (K : Type) [Field K] (z : Sp K ⟶ Y₀ T.X Z), ∃! p : Sp K ⟶ C.Y.X, Rel T.X.F C (z ≫ inc₀ T.X Z) p :=
    GlobalTheory.T.flagModel_point_carries_unique_flagBundle_point T.X Z hX C hC (B Z) (j Z) f hπ hl hJ
  obtain ⟨h, hh, hR⟩ := GlobalTheory.T.exists_hom_of_fieldPoint_relation_proper (Y₀ T.X Z) C.Y.X T.Y.X (inc₀ T.X Z ≫ T.X.π) (C.π ≫ genι T.Y)
    (fun K _ z w => Rel T.X.F C (z ≫ inc₀ T.X Z) w)
    (fun K _ z w hw => by rw [← Category.assoc]; exact Rel.over T.X C hw)
    (fun K _ z => hU K z)
    (fun K K' _ _ ι z w hw => by
      have := GlobalTheory.T.flagModel_carriesSameFlags_fieldExtension T.X hX C K K' ι _ _ hw
      rwa [← Category.assoc] at this)
    (fun A _ _ _ u v huv hr => by
      have := GlobalTheory.T.flagModel_carriesSameFlags_specialise_valuationRing T.X hX C hC A (u ≫ inc₀ T.X Z) v (by simpa only [Category.assoc] using huv)
        (by simpa only [Category.assoc] using hr)
      simpa only [Category.assoc] using this)
  have : IsProper (inc₀ T.X Z ≫ T.X.π) := inferInstance
  have : IsProper (h ≫ C.π ≫ genι T.Y) := by rw [hh]; infer_instance
  have : IsProper h := IsProper.of_comp h (C.π ≫ genι T.Y)
  have := GlobalTheory.T.flagModel_to_flagBundle_locallyQuasiFinite T.flag C hC Z h hR
  have hiso := GlobalTheory.T.isIso_flagModel_flagBundle_over_moduli T.X Z hX C hC (B Z) (j Z) f hπ hJ h hU hR
  have hVo : Nonempty (Vo C) := by
    refine ⟨⟨genericPoint C.Y.X, ?_⟩⟩
    show C.π (genericPoint C.Y.X) ∈ Set.range T.Y.jQ
    letI := (GlobalTheory.ShFam.constF (RingEquiv.refl c.F) C.Y).toAlgebra
    have e1 := Scheme.Hom.comp_apply (GlobalTheory.ShFam.genericPt C.Y) C.π (IsLocalRing.closedPoint C.Y.Fn)
    have e2 := Scheme.Hom.comp_apply (GlobalTheory.AllWt.ptF C.y0) T.Y.jQ (IsLocalRing.closedPoint C.Y.Fn)
    rw [C.y0_x] at e2
    have h1 := e1.symm.trans e2
    have h2 : (GlobalTheory.ShFam.genericPt C.Y) (IsLocalRing.closedPoint C.Y.Fn) = genericPoint C.Y.X :=
      Scheme.fromSpecStalk_closedPoint
    rw [h2] at h1
    exact ⟨_, h1.symm⟩
  have hpre : (U₀ T.X Z : Set (Y₀ T.X Z)) ⊆ h ⁻¹ᵁ Vo C := by
    intro y hy
    show C.π (h y) ∈ Set.range T.Y.jQ
    have e : genι T.Y (C.π (h y)) = T.X.π (inc₀ T.X Z y) := by
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, ← hh]
    obtain ⟨x, hx⟩ : T.X.π (inc₀ T.X Z y) ∈ Set.range T.Y.j := hy
    refine ⟨x, (genι T.Y).isOpenEmbedding.injective ?_⟩
    rw [e, ← hx, Model.j, Scheme.Hom.comp_apply]
  have : Nonempty (h ⁻¹ᵁ Vo C) := by
    obtain ⟨v⟩ := hVo
    exact ⟨inv (h ∣_ Vo C) v⟩
  have : IsIntegral (h ⁻¹ᵁ Vo C).toScheme := isIntegral_of_isOpenImmersion (h ∣_ Vo C)
  have hirr : IsIrreducible ((h ⁻¹ᵁ Vo C : (Y₀ T.X Z).Opens) : Set (Y₀ T.X Z)) := by
    rw [← Scheme.Opens.range_ι, ← Set.image_univ]
    exact (IrreducibleSpace.isIrreducible_univ _).image _ (h ⁻¹ᵁ Vo C).ι.continuous.continuousOn
  have hdense : closure ((h ⁻¹ᵁ Vo C : (Y₀ T.X Z).Opens) : Set (Y₀ T.X Z)) = Set.univ :=
    ((dense_U₀ T.X Z).mono hpre).closure_eq
  have : IrreducibleSpace (Y₀ T.X Z) := (irreducibleSpace_def _).2 (by
    have := hirr.closure
    rw [hdense] at this
    exact this)
  have : IsIntegral (Y₀ T.X Z) := isIntegral_of_irreducibleSpace_of_isReduced _
  have := C.Y.isNormalScheme
  have : IsIso h := GlobalTheory.isIso_of_isProper_of_quasiFinite_of_birational h
    (fun y => inferInstance) (Vo C) hVo
  refine isVariety_of_iso T.X Z C h ?_ (by rw [hdim, (hB Z).2.1, dim_eq])
  rw [← hps, ← Category.assoc, hh, Category.assoc]

end GlobalTheory.VarFlag
end
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc

namespace GlobalTheory.ZarhinFam

open GlobalTheory.CechPic

theorem principal_zP : ∀ (h M d : ℕ) (S : Scheme.{0}) (t : S ⟶ Sp (cycAway M)) (c : SiegPre h M (zetaAway M) t) (B : Over S) [GrpObj B] [IsCommMonObj B] (Q : LB (c.A ⊗ B).left) (la : c.A ⟶ B) (mu : B ⟶ c.A) (hZ : GlobalTheory.ZarhinFam.ZData c d B Q la mu), 1 ≤ h → 3 ≤ M → Odd M → 0 < d → M.Coprime d → IsUnit ((d : ℕ) : Γ(S, ⊤)) → SiegKerBy c d → Out.RelAmple (GlobalTheory.ZarhinFam.Zob c.A B) ((GlobalTheory.ZarhinFam.zP c.A B c.isLB hZ.2.1.isLB d mu).pull (lift (𝟙 (GlobalTheory.ZarhinFam.Zob c.A B)) (𝟙 (GlobalTheory.ZarhinFam.Zob c.A B))).left) ∧ ∀ (T : Over S) (x : T ⟶ (GlobalTheory.ZarhinFam.Zob c.A B)), (∃ t : ((GlobalTheory.ZarhinFam.zP c.A B c.isLB hZ.2.1.isLB d mu).pull (lift (snd (GlobalTheory.ZarhinFam.Zob c.A B) T ≫ x) (fst (GlobalTheory.ZarhinFam.Zob c.A B) T)).left).Gen, t.IsGen) → x = 1 := by
  intro h M d S t c B _ _ Q la mu hZ _ _ _ hd _ hunit hK
  refine ⟨?_, fun T x hx => ?_⟩
  · have hAb : IsAbelianScheme (Zob c.A B) := AbelianSchemeGerms.isAbelianScheme_tensor _ _
      (AbelianSchemeGerms.isAbelianScheme_powObj c.A c.ab 3) (AbelianSchemeGerms.isAbelianScheme_powObj B hZ.1 3)
    have := hAb.proper
    have hA : Out.RelAmple c.A c.diag := hK.1
    have huniv : ∀ (T : Over S) (y : Fin 8 → (T ⟶ c.A)), ∃! x : T ⟶ Out.powObj c.A 8,
        ∀ u, x ≫ Out.powPr c.A u = y u := fun T y =>
      ⟨(Out.powIsLimit c.A 8).lift (Fan.mk T y), fun u => (Out.powIsLimit c.A 8).fac (Fan.mk T y) ⟨u⟩,
        fun x hx => (Out.powIsLimit c.A 8).uniq (Fan.mk T y) x fun u => hx u.as⟩
    have h8 := GlobalTheory.PosDefAmple.relAmple_linComb_of_posDef GlobalTheory.SemiRigid.globalFns h M 8 _ _ S t c
      (Out.powObj c.A 8) (Out.powPr c.A) (zW d) (fun u => inferInstance) huniv hA (GlobalTheory.T.zarhinTriangularMatrix_symmetrisation_posDef d hd)
    have := GlobalTheory.T.isAffineHom_zarhinProduct_to_eighthPower h M d S t c B Q la mu hZ hd hunit
    have hF : (LB.LinComb c.P (K := Fin 8 × Fin 8)
        (fun uv => (lift (Out.powPr c.A uv.1) (Out.powPr c.A uv.2)).left) (fun uv => zW d uv.1 uv.2)).IsLB :=
      LB.isLB_linComb c.isLB _ _
    have hp := GlobalTheory.PosDefAmple.relAmple_pull_of_isAffineHom (zphi c.A B mu) hF h8
    have hzP := zarhinBundle_isLineBundle c.A B c.isLB hZ.2.1.isLB d mu
    refine GlobalTheory.PosDefAmple.relAmple_of_nsmul (pull_isLB hzP _) (pull_isLB hF _) (N := d) hd ?_ hp

    rw [cls_pull hzP, cls_zP, cls_pull hF, cls_linComb c.isLB, GlobalTheory.T.nsmul_zarhinDiagonalClass_eq_form h M d S t c B Q la mu hZ hd, map_sum]
    refine Finset.sum_congr rfl fun kl _ => ?_
    rw [map_zsmul, ← pull_comp, ← Over.comp_left, comp_lift, zphi_powPr, zphi_powPr]
  · have hla := hZ.2.2.2.1
    have hmu := hZ.2.2.2.2.1
    let f : (T ⟶ c.A) →* (T ⟶ B) := MonoidHom.mk' (fun a => a ≫ la) (fun a b => MonObj.mul_comp a b la)
    let g : (T ⟶ B) →* (T ⟶ c.A) := MonoidHom.mk' (fun a => a ≫ mu) (fun a b => MonObj.mul_comp a b mu)
    have hfg : ∀ a, g (f a) = a ^ d := fun a => by
      change (a ≫ la) ≫ mu = a ^ d
      rw [Category.assoc, hZ.2.2.2.2.2.1, MonObj.comp_pow, Category.comp_id]
    obtain ⟨hu, hv⟩ := GlobalTheory.T.zarhin_kernel_linearAlgebra_trivial d (T ⟶ c.A) (T ⟶ B) f g hd hfg (fun i => x ≫ pa c.A B i) (fun j => x ≫ pb c.A B j)
      (fun i => by simpa [f, Category.assoc] using GlobalTheory.T.zarhinBundle_kernel_firstCoord_equations h M d S t c B Q la mu hZ T x hx i)
      (fun j => GlobalTheory.T.zarhinBundle_kernel_secondCoord_equations h M d S t c B Q la mu hZ T x hx j)
      (GlobalTheory.T.zarhinBundle_kernel_of_secondCoord_trivial h M d S t c B Q la mu hZ T x hx)
    have e1 : x ≫ fst _ _ = 1 := (Out.powIsLimit c.A 4).hom_ext fun ⟨i⟩ => by
      change (x ≫ fst _ _) ≫ Out.powPr c.A i = 1 ≫ Out.powPr c.A i
      rw [MonObj.one_comp]
      exact (Category.assoc _ _ _).trans (hu i)
    have e2 : x ≫ snd _ _ = 1 := (Out.powIsLimit B 4).hom_ext fun ⟨j⟩ => by
      change (x ≫ snd _ _) ≫ Out.powPr B j = 1 ≫ Out.powPr B j
      rw [MonObj.one_comp]
      exact (Category.assoc _ _ _).trans (hv j)
    ext1
    · rw [e1, MonObj.one_comp]
    · rw [e2, MonObj.one_comp]

end GlobalTheory.ZarhinFam
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PerRoot

open IsDedekindDomain Polynomial

theorem exists_ord (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] :
    ∃ v : (FractionRing V)ˣ →* Multiplicative ℤ,
      (∀ x : (FractionRing V)ˣ, 0 ≤ (v x).toAdd → ∃ a : V, algebraMap V _ a = (x : FractionRing V)) ∧
      ∀ (x : (FractionRing V)ˣ) (a : V), algebraMap V _ a = (x : FractionRing V) →
        (0 < (v x).toAdd ↔ a ∈ maximalIdeal V) := by
  let w := (IsDiscreteValuationRing.maximalIdeal V).valuation (FractionRing V)
  have hw : ∀ x : (FractionRing V)ˣ, w x ≠ 0 := fun x => by simp [w]
  refine ⟨MonoidHom.mk' (fun x => Multiplicative.ofAdd (-WithZero.log (w x))) fun x y => ?_, fun x hx => ?_,
    fun x a ha => ?_⟩
  · rw [← ofAdd_add, Units.val_mul, map_mul, WithZero.log_mul (hw x) (hw y), neg_add]
  · refine IsDiscreteValuationRing.exists_lift_of_le_one ?_
    simp only [MonoidHom.mk'_apply, toAdd_ofAdd, neg_nonneg] at hx
    exact (WithZero.log_le_log (hw x) one_ne_zero).1 (by simpa using hx)
  · simp only [MonoidHom.mk'_apply, toAdd_ofAdd, neg_pos]
    have h1 : WithZero.log (w x) < 0 ↔ w x < 1 := by
      simpa using WithZero.log_lt_log (hw x) one_ne_zero
    rw [h1, ← ha]
    exact HeightOneSpectrum.valuation_lt_one_iff_mem _ a

theorem exists_nthRoots_ext (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    [IsAdicComplete (maximalIdeal V) V] [CharZero V] {I : Type} [Fintype I] (a : I → V) {n : ℕ} (hn : 1 ≤ n) :
    ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsDiscreteValuationRing W)
      (_ : IsAdicComplete (maximalIdeal W) W) (f : V →+* W) (s : I → W),
      Function.Injective f ∧ f.Finite ∧ IsLocalHom f ∧ ∀ k, s k ^ n = f (a k) := by
  classical
  let K := FractionRing V
  haveI : CharZero K := algebraRat.charZero _
  let p : I → K[X] := fun k => X ^ n - C (algebraMap V K (a k))
  have hp : ∀ k, (p k).Monic := fun k => monic_X_pow_sub_C _ (by omega)
  let L := (∏ k, p k).SplittingField
  have hsp : ((∏ k, p k).map (algebraMap K L)).Splits := SplittingField.splits _
  have hroot : ∀ k, ∃ t : L, t ^ n = algebraMap K L (algebraMap V K (a k)) := fun k => by
    have h0 : (∏ k, p k).map (algebraMap K L) ≠ 0 :=
      ((monic_prod_of_monic _ _ fun k _ => hp k).map _).ne_zero
    have h1 : ((p k).map (algebraMap K L)).Splits :=
      hsp.of_dvd h0 (Polynomial.map_dvd _ (Finset.dvd_prod_of_mem _ (Finset.mem_univ k)))
    obtain ⟨t, ht⟩ := h1.exists_eval_eq_zero (by
      rw [(hp k).degree_map, degree_X_pow_sub_C (by omega)]
      exact_mod_cast (by omega : n ≠ 0))
    refine ⟨t, ?_⟩
    simpa [p, sub_eq_zero] using ht
  choose t ht using hroot
  obtain ⟨W, _, _, _, _, _, _, _, hc, hfin, hinj, hloc, hint, -⟩ :=
    GlobalTheory.SS.exists_complete_dvr_finite_extension V K L
  have hs : ∀ k, t k ∈ Set.range (algebraMap W L) := fun k => hint _
    ⟨X ^ n - C (a k), monic_X_pow_sub_C _ (by omega), by simp [ht]⟩
  choose s hs using hs
  refine ⟨W, inferInstance, inferInstance, inferInstance, inferInstance, algebraMap V W, s, hinj,
    RingHom.finite_algebraMap.2 hfin, hloc, fun k => IsFractionRing.injective W L ?_⟩
  rw [map_pow, hs, ht]
  exact (RingHom.congr_fun hc (a k)).symm

theorem exists_form {G X : Type} [CommGroup G] [AddCommGroup X] (v : G →* Multiplicative ℤ) (q : X → X → G)
    (hsym : ∀ x y, q x y = q y x) (hadd : ∀ x x' y, q (x + x') y = q x y * q x' y) :
    ∃ β : LinearMap.BilinForm ℤ X, ∀ x y, β x y = (v (q x y)).toAdd := by
  have hadd' : ∀ x y y', q x (y + y') = q x y * q x y' := fun x y y' => by
    rw [hsym, hadd, hsym y, hsym y']
  let F : X → X →ₗ[ℤ] ℤ := fun x =>
    (AddMonoidHom.mk' (fun y => (v (q x y)).toAdd) fun y y' => by simp [hadd']).toIntLinearMap
  exact ⟨(AddMonoidHom.mk' F fun x x' => LinearMap.ext fun y => by simp [F, hadd]).toIntLinearMap,
    fun x y => rfl⟩

theorem isSymBasis_of_basis {X I : Type} [AddCommGroup X] (ε : Module.Basis I ℤ (balForms (id : ℤ → ℤ) X)) :
    IsSymBasis fun k => (ε k : LinearMap.BilinForm ℤ X) := by
  refine ⟨fun k => mem_balForms_int.1 (ε k).2, ε.linearIndependent.map' (Submodule.subtype _) (by simp),
    fun β hβ => ?_⟩
  have h := Submodule.mem_map_of_mem (f := (balForms (id : ℤ → ℤ) X).subtype)
    (ε.mem_span ⟨β, mem_balForms_int.2 hβ⟩)
  rw [Submodule.map_span, ← Set.range_comp] at h
  exact h

theorem exists_roots_of_periods : ∀ (g n : ℕ) (φ : InvFun ℤ), IsPolFan id g φ → 1 ≤ n → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], IsCN V → IsDiscreteValuationRing V → ∀ (r : ℕ), r ≤ g → ∀ (q : (Fin r → ℤ) → (Fin r → ℤ) → (FractionRing V)ˣ), (∀ a b, q a b = q b a) → (∀ a a' b, q (a + a') b = q a b * q a' b) → (∀ a, a ≠ 0 → ∃ w ∈ maximalIdeal V, w ≠ 0 ∧ (q a a : FractionRing V) = algebraMap V _ w) → ∃ (m N : ℕ) (ε : Module.Basis (Fin m ⊕ Fin N) ℤ (balForms (id : ℤ → ℤ) (Fin r → ℤ))), IsCone id φ (fun k => (ε (.inl k) : LinearMap.BilinForm ℤ (Fin r → ℤ))) ∧ (∀ x, x ≠ 0 → ∃ k, 0 < (ε (.inl k) : LinearMap.BilinForm ℤ (Fin r → ℤ)) x x) ∧ ∃ (V' : Type) (_ : CommRing V') (_ : IsDomain V') (_ : IsLocalRing V') (f : V →+* V') (fK : FractionRing V →+* FractionRing V') (s : Fin m ⊕ Fin N → V'), IsCN V' ∧ IsDiscreteValuationRing V' ∧ Function.Injective f ∧ f.Finite ∧ IsLocalHom f ∧ (∀ a, fK (algebraMap V _ a) = algebraMap V' _ (f a)) ∧ (∀ k, s (.inl k) ∈ maximalIdeal V' ∧ s (.inl k) ≠ 0) ∧ (∀ k, IsUnit (s (.inr k))) ∧ ∀ a b, fK (q a b : FractionRing V) = ∏ k, algebraMap V' _ (s k) ^ ((n : ℤ) * (ε k : LinearMap.BilinForm ℤ (Fin r → ℤ)) a b) := by
  intro g n φ hφ hn V _ _ _ hV hD r hr q hsym hadd hpos
  obtain ⟨-, -, hcomp, hchar⟩ := hV
  obtain ⟨v, hv1, hv2⟩ := exists_ord V
  obtain ⟨β, hβ⟩ := exists_form v q hsym hadd
  have hβs : ∀ x y, β x y = β y x := fun x y => by rw [hβ, hβ, hsym]
  have hβp : ∀ x, x ≠ 0 → 0 < β x x := fun x hx => by
    obtain ⟨w, hw, -, h⟩ := hpos x hx
    rw [hβ]
    exact (hv2 _ w h.symm).2 hw
  have hβn : ∀ x, 0 ≤ β x x := fun x => by
    by_cases hx : x = 0
    · simp [hx]
    · exact (hβp x hx).le
  obtain ⟨m, ga, c, hga, hc, hβc⟩ := GlobalTheory.ConeInterior.exists_pos_comb_int g φ hφ r hr β hβs
    (GlobalTheory.PolFan.TameZ.toReal_mem_psdCone_int (mem_balForms_int.2 hβs) hβn)
  obtain ⟨N, ε, hε⟩ := hga.basis
  have hεga : ∀ k, (ε (.inl k) : LinearMap.BilinForm ℤ (Fin r → ℤ)) = ga k := fun k => by rw [hε]
  have hsb := isSymBasis_of_basis ε
  obtain ⟨u, hu, -⟩ := existsUnique_coeff hsb q hsym hadd
  have hβv : ∀ x y, β x y = ∑ j, (c j : ℤ) * ga j x y := fun x y => by
    rw [hβc]; simp [LinearMap.sum_apply]
  have hvu : (fun k => v (u k)) = fun k => Multiplicative.ofAdd (Sum.elim (fun j => (c j : ℤ)) 0 k) := by
    refine eq_of_prod_zpow hsb _ _ fun x y => ?_
    simp_rw [← map_zpow, ← map_prod, ← hu]
    apply Multiplicative.toAdd.injective
    rw [← hβ, hβv, toAdd_prod, Fintype.sum_sum_type]
    simp [hεga, mul_comm]
  have hvk : ∀ k, (v (u k)).toAdd = Sum.elim (fun j => (c j : ℤ)) 0 k := fun k => by
    rw [congrFun hvu k]; rfl
  choose a ha using fun k => hv1 (u k) (by rw [hvk]; cases k <;> simp)
  have ha0 : ∀ k, a k ≠ 0 := fun k h => (u k).ne_zero (by rw [← ha, h, map_zero])
  obtain ⟨W, _, _, _, _, f, s, hinj, hfin, hloc, hs⟩ := exists_nthRoots_ext V a hn
  have hinj' : Function.Injective ((algebraMap W (FractionRing W)).comp f) :=
    (IsFractionRing.injective W _).comp hinj
  have hfK : ∀ b, IsFractionRing.lift (K := FractionRing V) hinj' (algebraMap V _ b) =
      algebraMap W (FractionRing W) (f b) := fun b => IsFractionRing.lift_algebraMap hinj' b
  refine ⟨m, N, ε, by simpa only [hεga] using hga, fun x hx => ?_, W, inferInstance, inferInstance, inferInstance, f,
    IsFractionRing.lift hinj', s, ⟨inferInstance, inferInstance, inferInstance, ?_⟩, inferInstance, hinj, hfin, hloc,
    hfK, fun k => ⟨?_, fun h => ?_⟩, fun k => ?_, fun x y => ?_⟩
  · by_contra h
    push_neg at h
    have h1 := hβp x hx
    rw [hβv] at h1
    exact h1.not_ge (Finset.sum_nonpos fun j _ =>
      mul_nonpos_of_nonneg_of_nonpos (Int.natCast_nonneg _) (hεga j ▸ h j))
  · exact charZero_of_injective_ringHom hinj
  · have h1 : a (.inl k) ∈ maximalIdeal V := (hv2 _ _ (ha _)).1 (by rw [hvk]; simpa using hc k)
    intro h
    exact h1 (isUnit_of_map_unit f _ (hs _ ▸ h.pow n))
  · refine ha0 (.inl k) (hinj ?_)
    rw [← hs, h, map_zero, zero_pow (by omega)]
  · have h1 : a (.inr k) ∉ maximalIdeal V := fun h => by
      have := (hv2 _ _ (ha _)).2 h
      rw [hvk] at this
      simp at this
    have h2 : IsUnit (s (.inr k) ^ n) := hs _ ▸ (not_not.1 h1 : IsUnit (a (.inr k))).map f
    exact (isUnit_pow_iff (by omega)).1 h2
  · rw [hu, Units.coe_prod, map_prod]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [Units.val_zpow_eq_zpow_val, map_zpow₀, ← ha, hfK, ← hs, map_pow, zpow_mul, zpow_natCast]

end GlobalTheory.PerRoot
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor


theorem _root_.GlobalTheory.T.exists_local_symplecticSimilitude_classifyingMaps : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N h M : ℕ),
  3 ≤ N → N.Coprime p → 3 ≤ M → Odd M → M.Coprime p →
  ∀ (X : Scheme.{0}) (s : X ⟶ Sp R) (s₁ : X ⟶ Sp (cycAway M)) (u : Obj b N s)
    (lev : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over X) ⟶ u.A)),
    IsSympLev u.P h M (zetaAway M) s₁ lev → HarrisTaylorSymplecticLevelFamilyUniversalProperty b N h M s s₁ u lev →
    ∀ ρ : sympSimGrp h M → (X ⟶ X), SympActs s s₁ u lev ρ →
    ∀ (T : Scheme.{0}) (t : T ⟶ Sp R) (o : Obj b N t) (x x' : T ⟶ X), x ≫ s = t → x' ≫ s = t →
      Nonempty (ObjMap o u x) → Nonempty (ObjMap o u x') →
      ∀ q : T, ∃ (V : T.Opens) (a : sympSimGrp h M), q ∈ V ∧ V.ι ≫ x ≫ ρ a = V.ι ≫ x' := by
  first | (exact @GlobalTheory.HTLocSim.exists_local_similitude) | (exact GlobalTheory.HTLocSim.exists_local_similitude) | (intros; apply GlobalTheory.HTLocSim.exists_local_similitude  <;> assumption)
end
