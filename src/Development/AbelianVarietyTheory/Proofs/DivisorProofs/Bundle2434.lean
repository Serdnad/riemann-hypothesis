module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StoneVonNeumannSchwartzBruhatTransverseLagrangia
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsoOverOfIsOpenImmersion
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsUniqueLbIsoPullEqOfCoheightLeOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2395
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
public import Development.AbelianVarietyTheory.Definitions.Divisors.KernelNormConstantSpec
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2394
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1668
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1667
public import Development.AbelianVarietyTheory.Definitions.Divisors.LevelOfOfSameBut
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2290
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle004
public import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle014
public import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2383
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2198
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2243
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2101
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2179
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
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle003
import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsCoprimeOfNatCast
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomogeneousCompIdeal
public import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
public import Development.AbelianVarietyTheory.Definitions.Divisors.UnitaryWeightExponentVectorSignatureWeightMuZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2325

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

open scoped GlobalTheory.VacAny


theorem _root_.GlobalTheory.T.stoneVonNeumann_schwartzBruhat_transverseLagrangians : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k]
    [Invertible (2 : k)] {κ : Type} [Fintype κ] {n d : ℕ} (ψ0 : AddChar k ℂ), Continuous ψ0 →
    (∀ x : k, (∀ y ∈ 𝒪[k], ψ0 (x * y) = 1) ↔ x ∈ 𝒪[k]) →
    ∀ (wT wM : Matrix (Fin n) (Fin d) k →+ (κ → k) × (κ → k)),
    (∀ Y Y', (wT Y).1 ⬝ᵥ (wT Y').2 - (wT Y').1 ⬝ᵥ (wT Y).2 = 0) →
    (∀ z z', (wM z).1 ⬝ᵥ (wM z').2 - (wM z').1 ⬝ᵥ (wM z).2 = 0) →
    (∀ Y z, (wT Y).1 ⬝ᵥ (wM z).2 - (wM z).1 ⬝ᵥ (wT Y).2 = ∑ i, ∑ j, Y i j * z i j) →
    (∀ w, ∃ Y z, wT Y + wM z = w) →
    ∃ ι : ((κ → k) → ℂ) →ₗ[ℂ] (Matrix (Fin n) (Fin d) k → ℂ),
      Set.BijOn ι (GlobalTheory.WeilM.SB (κ → k) : Set _) (GlobalTheory.WeilM.SB (Matrix (Fin n) (Fin d) k) : Set _) ∧
      (∀ Y, ∀ φ ∈ GlobalTheory.WeilM.SB (κ → k), ι (GlobalTheory.WeilM.schr ψ0 (wT Y) φ) = fun Y' => ι φ (Y' + Y)) ∧
      (∀ z, ∀ φ ∈ GlobalTheory.WeilM.SB (κ → k), ι (GlobalTheory.WeilM.schr ψ0 (wM z) φ) = fun Y' => ψ0 (∑ i, ∑ j, Y' i j * z i j) * ι φ Y') := by
  first | exact @GlobalTheory.StoneVN.intertwiner_matrix | exact GlobalTheory.StoneVN.intertwiner_matrix | (intros; apply GlobalTheory.StoneVN.intertwiner_matrix <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep

namespace GlobalTheory.ModifCanon
open GlobalTheory.Vanishing.H0 GlobalTheory.TangentOrigin

theorem stalkMap_bijective_of_isIso_restrict : ∀ (Y X : Scheme.{0}) (σ : X ⟶ Y) (U : Y.Opens), IsIso (σ ∣_ U) →
    ∀ x : X, x ∈ σ ⁻¹ᵁ U → Function.Bijective (σ.stalkMap x).hom := by
  intro Y X σ U h x hx
  have e := morphismRestrictStalkMap σ U ⟨x, hx⟩
  have h1 : IsIso ((σ ∣_ U).stalkMap ⟨x, hx⟩) := ((isIso_iff_isIso_stalkMap (σ ∣_ U)).1 h).2 _
  have h2 : IsIso (σ.stalkMap x) := ((MorphismProperty.isomorphisms _).arrow_mk_iso_iff e).1 h1
  exact ConcreteCategory.bijective_of_isIso _

theorem isUnit_val_of_isUnit_germ : ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) (p : Y ⟶ Sp k) (B : LB Y) (O : Y.Opens)
    (x : Sp ℂ ⟶ Y) (i : B.ι) (hO : ⊤ ≤ x ⁻¹ᵁ O) (hi : ⊤ ≤ x ⁻¹ᵁ B.U i) (f : H0 p B O) (e : Sp ℂ)
    (hy : x e ∈ O) (hiy : x e ∈ B.U i), IsUnit (H0.germ i (x e) hy hiy f) → IsUnit (H0.val x i hO hi f) := by
  intro k _ Y p B O x i hO hi f e hy hiy hu
  have hb : x e ∈ Y.basicOpen (f.loc i) := (Y.mem_basicOpen _ _ (Vanishing.memInf hy hiy)).2 hu
  have hV : ⊤ ≤ x ⁻¹ᵁ Y.basicOpen (f.loc i) := fun y _ => by rw [Subsingleton.elim y e]; exact hb
  rw [H0.val_apply, ← evalPt_res x (Y.basicOpen_le (f.loc i)) _ hV]
  exact (RingedSpace.isUnit_res_basicOpen Y.toLocallyRingedSpace.toRingedSpace (f.loc i)).map _

end GlobalTheory.ModifCanon

namespace GlobalTheory.ModifCanon

open GlobalTheory.Vanishing.H0 GlobalTheory.TangentOrigin

variable {X Y : Scheme.{0}}

abbrev jacChart {K' : LB X} {K B : LB Y} (σ : X ⟶ Y) (hK' : K'.IsLB) (hK : K.IsLB) (hB : B.IsLB) :
    ProdChart (LB.div K' (K.pull σ)) ((tens K B).pull σ) (tens K' (B.pull σ)) where
  isLB₁ := LB.isLB_div hK' (LB.isLB_pull hK σ)
  isLB₂ := LB.isLB_pull (isLB_tens hK hB) σ
  isLB₃ := isLB_tens hK' (LB.isLB_pull hB σ)
  τ := K'.ι × K.ι × B.ι
  a t := (t.1, pIdx K σ t.2.1)
  b t := pIdx (tens K B) σ (t.2.1, t.2.2)
  c t := (t.1, pIdx B σ t.2.2)
  cover x := by
    obtain ⟨i, hi⟩ := exists_chart hK' x
    obtain ⟨j, hj⟩ := exists_chart hK (σ x)
    obtain ⟨l, hl⟩ := exists_chart hB (σ x)
    exact ⟨(i, j, l), ⟨hi, mem_pIdx.2 hj⟩, mem_pIdx.2 ⟨hj, hl⟩, hi, mem_pIdx.2 hl⟩
  rule x t t' e e' := by
    rw [tr_tens _ _ x e.2.2 e'.2.2, tr_div _ _ x e.1 e'.1, tr_pull _ σ x e.2.1 e'.2.1,
      tr_pull _ σ x e.2.2.2 e'.2.2.2, tr_pull _ σ x e.1.2 e'.1.2,
      tr_tens _ _ (σ x) (mem_pull.1 e.2.1) (mem_pull.1 e'.2.1), map_mul, mul_assoc]
    exact congrArg (tr K' x t.1 t'.1 * ·) (inv_mul_cancel_left _ _).symm

theorem val_restr {k : Type} [CommRing k] {p : Y ⟶ Sp k} {B : LB Y} {O O' : Y.Opens} (x : Sp ℂ ⟶ Y) (i : B.ι)
    (h : O' ≤ O) (hO' : ⊤ ≤ x ⁻¹ᵁ O') (hO : ⊤ ≤ x ⁻¹ᵁ O) (hi : ⊤ ≤ x ⁻¹ᵁ B.U i) (f : H0 p B O) :
    H0.val x i hO' hi (H0.restr h f) = H0.val x i hO hi f :=
  evalPt_res x (inf_le_inf_right _ h) _ _ (f.loc i)

theorem exists_push_sections : ∀ (F : Type) [Field F] [CharZero F] (Y : Scheme.{0}) [IsIntegral Y] (p : Y ⟶ Sp F) (d : ℕ) [SmoothOfRelativeDimension d p] (U : Y.Opens) (M : Modif p U d) (K : CanonLB p d) (K' : CanonLB M.str d) (B : LB Y), IsProjOver p → (U : Set Y).Nonempty → B.IsLB → ∃ Ψ : H0 M.str (tens K'.bundle (B.pull M.σ)) ⊤ → H0 p (tens K.bundle B) ⊤, ∀ (z : Sp ℂ ⟶ M.X), ⊤ ≤ z ⁻¹ᵁ M.opn → ∀ (k' : (tens K'.bundle (B.pull M.σ)).ι) (hk' : ⊤ ≤ z ⁻¹ᵁ (tens K'.bundle (B.pull M.σ)).U k') (k : (tens K.bundle B).ι) (hk : ⊤ ≤ (z ≫ M.σ) ⁻¹ᵁ (tens K.bundle B).U k), ∃ lam : ℂˣ, ∀ g, H0.val (z ≫ M.σ) k le_top hk (Ψ g) = lam * H0.val z k' le_top hk' g := by
  intro F _ _ Y _ p d _ U M K K' B hproj hU hB
  have : Smooth p := SmoothOfRelativeDimension.smooth d p
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian p
  have : GlobalTheory.IsNormalScheme Y := isNormalScheme_of_smooth p
  have : Nonempty U := hU.to_subtype
  have := M.iso
  have hXi : IsIntegral M.X := GlobalTheory.T.isIntegral_smoothProjectiveModification_of_nonempty F Y p U d M hU
  obtain ⟨J, hJ⟩ := GlobalTheory.T.exists_jacobian_section_isUnit_germ_of_localIso F Y M.X p M.σ d K K'
  have hL : (tens K.bundle B).IsLB := isLB_tens K.isLB hB
  let C := jacChart M.σ K'.isLB K.isLB hB
  have hopn : ∀ x ∈ M.opn, Function.Bijective (M.σ.stalkMap x).hom :=
    stalkMap_bijective_of_isIso_restrict Y M.X M.σ U M.iso
  have hJU : NowhereZero (H0.restr (le_top : M.opn ≤ ⊤) J) := fun x hx a ha => by
    rw [germ_restr]; exact hJ x (hopn x hx) a ha
  have hT : M.opn ≤ M.σ ⁻¹ᵁ (⊤ : Y.Opens) := fun x _ => memTop (M.σ x)
  have ext : ∀ g : H0 M.str (tens K'.bundle (B.pull M.σ)) ⊤, ∃ s : H0 p (tens K.bundle B) ⊤,
      C.mul (H0.restr le_top J) (H0.pull M.σ hT s) = H0.restr le_top g := by
    intro g
    obtain ⟨s₀, hs₀⟩ := (M.bijective_pull hL).2 ((C.mulEquiv hJU).symm (H0.restr le_top g))
    have rel : C.mul (H0.restr le_top J) (H0.pull M.σ le_rfl s₀) = H0.restr le_top g := by
      rw [hs₀]; exact (C.mulEquiv hJU).apply_symm_apply _
    obtain ⟨t, ht⟩ := (exists_sec_res_eq_iff hL (W := U) (LB.coord_mem s₀)).2 (fun x hx1 _ => by
      have := IsNormalScheme.isDiscreteValuationRing_stalk hx1
      obtain ⟨x', rfl, hb⟩ := GlobalTheory.T.exists_bijective_stalkMap_over_dvrPoint F Y p U d M hproj hU x this
      obtain ⟨i, hi⟩ := exists_chart hL (M.σ x')
      have : Nonempty ((tens K.bundle B).U i) := ⟨⟨_, hi⟩⟩
      have hne := nonempty_inf_of_isIntegral U ((tens K.bundle B).U i)
      exact ⟨i, hne, hi, GlobalTheory.T.germ_mem_range_stalk_of_pullback_mul_localIso F Y M.X p M.σ U _ _ _ C J g s₀ rel x' hb (hJ x' hb) i hi⟩)
    refine ⟨H0.ofSec p ⊤ t, ?_⟩
    have e : H0.restr (le_top : U ≤ ⊤) (H0.ofSec p ⊤ t) = s₀ := by
      rw [restr_ofSec]; exact LB.sec_ext fun i => ht i
    rw [← rel, ← e, pull_restr]
  choose Ψ hΨ using ext
  refine ⟨Ψ, fun z hz k' hk' k hk => ?_⟩
  obtain ⟨e⟩ : Nonempty (Sp ℂ) := inferInstance
  have all : ∀ (V : M.X.Opens), z e ∈ V → ⊤ ≤ z ⁻¹ᵁ V := fun V hV y _ => by
    rw [Subsingleton.elim y e]; exact hV
  have he : z e ∈ M.opn := hz trivial
  obtain ⟨t, ha, hb, hc⟩ := C.cover (z e)
  have ha' := all _ ha
  have hb' := all _ hb
  have hc' := all _ hc
  have hb'' : ⊤ ≤ (z ≫ M.σ) ⁻¹ᵁ (tens K.bundle B).U ((C.b t) PUnit.unit) := fun y _ => by
    rw [Subsingleton.elim y e]; exact mem_pull.1 hb
  have hJv := isUnit_val_of_isUnit_germ F M.X M.str _ M.opn z (C.a t) hz ha' (H0.restr le_top J) e he ha
    (hJU _ he _ ha)
  obtain ⟨T1, hT1, e2⟩ : ∃ T1 : ℂ, T1 ≠ 0 ∧ ∀ g, H0.val z k' le_top hk' g = T1 * H0.val z (C.c t) le_top hc' g :=
    ⟨_, ((Units.isUnit _).map _).ne_zero, fun g => val_change (p := M.str) (O := ⊤) z k' (C.c t) le_top hk' hc' g⟩
  obtain ⟨T2, hT2, e1⟩ : ∃ T2 : ℂ, T2 ≠ 0 ∧ ∀ g, H0.val (z ≫ M.σ) k le_top hk (Ψ g) =
      T2 * H0.val (z ≫ M.σ) ((C.b t) PUnit.unit) le_top hb'' (Ψ g) :=
    ⟨_, ((Units.isUnit _).map _).ne_zero, fun g => val_change (p := p) (O := ⊤) (z ≫ M.σ) k ((C.b t) PUnit.unit) le_top hk hb'' (Ψ g)⟩
  refine ⟨Units.mk0 (T2 / (H0.val z (C.a t) hz ha' (H0.restr le_top J) * T1))
    (div_ne_zero hT2 (mul_ne_zero hJv.ne_zero hT1)), fun g => ?_⟩
  have e3 := C.val_mul (H0.restr le_top J) (H0.pull M.σ hT (Ψ g)) t z hz ha' hb' hc'
  rw [hΨ g, val_restr z _ le_top hz le_top] at e3
  have e4 := val_pull M.σ hT z (C.b t) hz hb' le_top hb'' (Ψ g)
  rw [e1, e2, e3, ← e4, Units.val_mk0]
  rw [div_mul_eq_mul_div, eq_div_iff (mul_ne_zero hJv.ne_zero hT1)]
  ring

end GlobalTheory.ModifCanon
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FunObj.FockChi

theorem fockIn_chi_zero : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GlobalTheory.ChiGrid.GridData L sc} (W : G.Weil) {U : Set T} (N : GlobalTheory.FunObj.Std G U) (δ t0 : ℂ), Formalism.MainNotions.StandardLatticesGL3.Crv D D.host.ccK δ → δ ≠ 0 → Formalism.MainNotions.GL3Theta.IsTwoTorsionPointUnkilled D (Formalism.MainNotions.TaylorLogMetric.lamOf D D.host.ccK δ) t0 → ∀ i : ℕ, i + 1 ≤ D.R.m → ∀ e0 : Formalism.MainNotions.TaylorLogMetric.VC D (G.pS (.chi i D.R.m : Pair T)).rank (G.pT (.chi i D.R.m : Pair T)).rank → ℂ, Formalism.MainNotions.StandardLatticesGL3.oddE0 D D.host.ccK δ t0 _ _ e0 → ∀ f, IsVacO W.ψ W.θ _ _ (G.cartS W.cart (.chi i D.R.m)) (G.onT W.cart (.chi i D.R.m)) (N.latS (.chi i D.R.m) : Set _) (N.latT (.chi i D.R.m) : Set _) f → ∃ c : ℂˣ, ∀ k : FVar D (G.pT (.chi i D.R.m : Pair T)).rank (G.pS (.chi i D.R.m : Pair T)).rank →₀ ℕ, GlobalTheory.FunObj.fockIn W N.frC (.chi i D.R.m) f (MvPolynomial.monomial k 1) 0 = c * starRingEnd ℂ ((k.prod fun v n => GlobalTheory.FunObj.period δ v.1 ^ n) * Formalism.MainNotions.GL3Theta.applyAt0 D (MvPolynomial.monomial k 1) e0) := by
  intro D T L sc G W U N δ t0 hc hδ ht i hi e0 he f hf
  have hcf := GlobalTheory.T.isVacuum_conj_of_negHermitianSpace _ _ _ _ _ _ _ _ f hf
  obtain ⟨c, hc'⟩ := GlobalTheory.T.fockJets_unitVacuum_eq_unit_mul_periodJets W.ψ W.θ (G.V (.grid (i + 1) D.R.m)) (G.V (.grid i D.R.m)) (W.cart (.grid (i + 1) D.R.m)) (W.cart (.grid i D.R.m))
    (N.fr _) (N.fr _) (N.fr_on _ ⟨hi, rfl⟩) (N.fr_on _ ⟨by omega, rfl⟩)
    (W.cart_is _ ⟨hi, le_rfl⟩) (W.cart_is _ ⟨by omega, le_rfl⟩) δ t0 hc hδ ht e0 he _ hcf
  refine ⟨Units.map (starRingEnd ℂ).toMonoidHom c, fun k => ?_⟩
  have h2 := GlobalTheory.T.fockVector_negHermitianSpace_conj_monomial W.ψ W.θ (G.V (.grid (i + 1) D.R.m)) (G.V (.grid i D.R.m)) (W.cart (.grid (i + 1) D.R.m)) (W.cart (.grid i D.R.m))
    (N.frC (.grid (i + 1) D.R.m)) (N.frC (.grid i D.R.m)) f hf.1 hf.2.inf k 0
  have e1 : N.frC (.grid (i + 1) D.R.m) = fun τ => (N.fr (.grid (i + 1) D.R.m)).1.map (tauE D τ) := rfl
  have e2 : N.frC (.grid i D.R.m) = fun τ => (N.fr (.grid i D.R.m)).1.map (tauE D τ) := rfl
  show pureTensorO _ _ _ _ _ _ _ _ f _ 0 = _
  rw [h2, e1, e2, hc' k, map_mul]
  rfl

end GlobalTheory.FunObj.FockChi
end

section

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open Formalism.BasicNotions Formalism.MainNotions Formalism.IndefR.Links Formalism.L2.Host GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp GlobalTheory.SeriesTie




namespace GlobalTheory.BigOn.Exp.Adapt

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem exists_ext_frac {A B : Type} [CommRing A] [IsDomain A] [CommRing B] [IsDomain B] [Algebra A B]
    (hinj : Function.Injective (algebraMap A B)) [Module.Finite A B] (f : FractionRing A →+* ℂ) :
    ∃ g : FractionRing B →+* ℂ, ∀ a : A, g (algebraMap B _ (algebraMap A B a)) = f (algebraMap A _ a) := by
  letI : Algebra A ℂ := (f.comp (algebraMap A (FractionRing A))).toAlgebra
  haveI : Algebra.IsIntegral A B := Algebra.IsIntegral.of_finite A B
  haveI : Algebra.IsAlgebraic A B := inferInstance
  haveI : Algebra.IsAlgebraic B (FractionRing B) := IsLocalization.isAlgebraic _ (nonZeroDivisors B)
  haveI : Algebra.IsAlgebraic A (FractionRing B) := Algebra.IsAlgebraic.trans A B (FractionRing B)
  have hA : Function.Injective (algebraMap A (FractionRing B)) := by
    rw [IsScalarTower.algebraMap_eq A B (FractionRing B)]
    exact (IsFractionRing.injective B (FractionRing B)).comp hinj
  have hC : Function.Injective (algebraMap A ℂ) :=
    f.injective.comp (IsFractionRing.injective A (FractionRing A))
  haveI : Module.IsTorsionFree A (FractionRing B) := Module.IsTorsionFree.of_smul_eq_zero fun r m h => by
    rw [Algebra.smul_def, mul_eq_zero] at h
    exact h.imp (fun h => hA (h.trans (map_zero _).symm)) id
  haveI : Module.IsTorsionFree A ℂ := Module.IsTorsionFree.of_smul_eq_zero fun r m h => by
    rw [Algebra.smul_def, mul_eq_zero] at h
    exact h.imp (fun h => hC (h.trans (map_zero _).symm)) id
  let g := IsAlgClosed.lift (M := ℂ) (R := A) (S := FractionRing B)
  refine ⟨g.toRingHom, fun a => ?_⟩
  have h := g.commutes a
  rw [IsScalarTower.algebraMap_apply A B (FractionRing B)] at h
  exact h

variable {D : D7}

theorem charOf_congr {Ω : Type} [Field Ω] [Algebra D.host.E Ω] (a : Recip D Ω) {R : Type} [CommRing R]
    (f f' : R →+* ℂ) (ψ : G D.host.E Ω →* Rˣ) (h : ∀ σ, f (ψ σ : Rˣ) = f' (ψ σ : Rˣ)) :
    GlobalTheory.SeriesTie.charOf a f ψ = GlobalTheory.SeriesTie.charOf a f' ψ := by
  have hv : ∀ x, ∃ σ, a.pull ψ x = ψ σ := by
    intro x
    unfold Recip.pull GlobalTheory.SeriesTie.descend
    split_ifs with hc
    · obtain ⟨σ, hσ⟩ := QuotientGroup.mk'_surjective _ (a.sym x)
      refine ⟨σ, ?_⟩
      rw [MonoidHom.comp_apply, ← hσ]
      rfl
    · exact ⟨1, by simp⟩
  refine MonoidHom.ext fun x => ?_
  obtain ⟨σ, hσ⟩ := hv x
  simp only [GlobalTheory.SeriesTie.charOf, MonoidHom.comp_apply, hσ]
  rw [show Units.map f.toMonoidHom (ψ σ) = Units.map f'.toMonoidHom (ψ σ) from Units.ext (h σ)]


open Classical in
def withTau (ρ : Setup D.ntw) (t : D.ntw.Tw) (s : Bool) (τ : ℂ ≃+* ℂ) : Setup D.ntw :=
  { ρ with
    e := fun i b => if i = t ∧ b = s then τ.toRingHom.comp (ρ.e i b) else ρ.e i b
    ek := fun i b k => if i = t ∧ b = s then τ.toRingHom.comp (ρ.ek i b k) else ρ.ek i b k }


open Classical in
theorem withTau_e (ρ : Setup D.ntw) (t : D.ntw.Tw) (s : Bool) (τ : ℂ ≃+* ℂ) (i : D.ntw.Tw) (b : Bool) :
    (withTau ρ t s τ).e i b = if i = t ∧ b = s then τ.toRingHom.comp (ρ.e i b) else ρ.e i b := rfl


open Classical in
theorem withTau_ek (ρ : Setup D.ntw) (t : D.ntw.Tw) (s : Bool) (τ : ℂ ≃+* ℂ) (i : D.ntw.Tw) (b : Bool) (k : ℕ) :
    (withTau ρ t s τ).ek i b k = if i = t ∧ b = s then τ.toRingHom.comp (ρ.ek i b k) else ρ.ek i b k := rfl

theorem withTau_good {ρ : Setup D.ntw} (hρ : ρ.Good) (t : D.ntw.Tw) (s : Bool) (τ : ℂ ≃+* ℂ)
    (hfix : ∀ y, τ (embLL0 D y) = embLL0 D y)
    (hδ : ∀ σ, τ (ρ.eO t s (algebraMap (D.ntw.O0 t) (D.ntw.O t)
        ((Formalism.MainNotions.BlochKatoReduction.Gen.psiAt s (D.ntw.delta t) σ : (D.ntw.O0 t)ˣ) : D.ntw.O0 t))) =
      ρ.eO t s (algebraMap (D.ntw.O0 t) (D.ntw.O t) ((Formalism.MainNotions.BlochKatoReduction.Gen.psiAt s (D.ntw.delta t) σ : (D.ntw.O0 t)ˣ) : D.ntw.O0 t))) :
    (withTau ρ t s τ).Good := by
  refine ⟨hρ.rc, hρ.ch, hρ.bad_ne, hρ.goodSetup_bad_mem_badPlaces, hρ.goodSetup_badPlaces_conj, hρ.goodSetup_placesOverTwo_subset, hρ.goodSetup_count_eq_zero_off_badPlaces, ?_, ?_, hρ.base, hρ.latS, hρ.latT, hρ.Pg,
    ?_, hρ.weil, hρ.classes⟩
  · intro i b x
    rw [withTau_e]
    split_ifs with h
    · show τ (ρ.e i b _) = _
      rw [hρ.e_LL0]
      exact hfix x
    · exact hρ.e_LL0 i b x
  · intro i b k x
    show (withTau ρ t s τ).ek i b k _ = (withTau ρ t s τ).e i b _
    rw [withTau_e, withTau_ek]
    split_ifs with h
    · exact congrArg τ (hρ.ek_e i b k x)
    · exact hρ.ek_e i b k x
  · intro i j b
    show (ρ.B i j b).de = twistOf ρ.rc (((withTau ρ t s τ).eO i b).comp (algebraMap (D.ntw.O0 i) (D.ntw.O i))) (ρ.ch i)
      (D.ntw.pD i) (Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i))
    rw [hρ.delta i j b]
    unfold twistOf
    have : GlobalTheory.SeriesTie.charOf ρ.rc ((ρ.eO i b).comp (algebraMap (D.ntw.O0 i) (D.ntw.O i))) (Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i)) =
        GlobalTheory.SeriesTie.charOf ρ.rc (((withTau ρ t s τ).eO i b).comp (algebraMap (D.ntw.O0 i) (D.ntw.O i)))
          (Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i)) := by
      refine charOf_congr _ _ _ _ fun σ => ?_
      show ρ.e i b _ = (withTau ρ t s τ).e i b _
      rw [withTau_e]
      split_ifs with h
      · obtain ⟨rfl, rfl⟩ := h
        exact (hδ σ).symm
      · rfl
    rw [this]

theorem ext_onSmallField {c : NChoice D} (hc : NChTie D c) (w : D.what₂.places.Pl) {ρ : Setup D.ntw} (hρ : ρ.Good)
    (g : FractionRing (c.Oe w) →+* ℂ)
    (hg : ∀ a : D.ntw.Ok (c.twI w) (c.k' w), g (algebraMap (c.Oe w) _ (algebraMap _ (c.Oe w) a)) =
      ρ.ek (c.twI w) (c.sd w) (c.k' w) (algebraMap _ _ a))
    (y : D.LL0) : g (c.embW w (y : D.what₂.LL)) = embLL0 D y := by
  obtain ⟨⟨y', z⟩, hz⟩ := IsLocalization.surj (nonZeroDivisors (D.ntw.O0 (c.twI w)))
    ((if c.sd w then D.ntw.emb0 (c.twI w) else D.ntw.emb0b (c.twI w)) y)
  have hz0 : (z : D.ntw.O0 (c.twI w)) ≠ 0 := nonZeroDivisors.coe_ne_zero z
  have e1 : ∀ x : D.ntw.O (c.twI w), ρ.ek (c.twI w) (c.sd w) (c.k' w)
      (algebraMap _ (FractionRing _) (algebraMap (D.ntw.O (c.twI w)) (D.ntw.Ok (c.twI w) (c.k' w)) x)) =
      ρ.e (c.twI w) (c.sd w) (algebraMap _ _ x) := hρ.ek_e (c.twI w) (c.sd w) (c.k' w)
  have h1 := congrArg g (hc.embedding_baseField_condition w y y' z hz0 hz)
  rw [map_mul, hg, hg, e1, e1] at h1
  have h2 : sideEmb D.ntw (c.twI w) (c.sd w) y * algebraMap (D.ntw.O (c.twI w)) (FractionRing (D.ntw.O (c.twI w)))
      (algebraMap (D.ntw.O0 (c.twI w)) (D.ntw.O (c.twI w)) z) =
      algebraMap _ _ (algebraMap (D.ntw.O0 (c.twI w)) (D.ntw.O (c.twI w)) y') := by
    have := congrArg (IsFractionRing.map (A := D.ntw.O0 (c.twI w)) (B := D.ntw.O (c.twI w))
      (K := FractionRing (D.ntw.O0 (c.twI w))) (L := FractionRing (D.ntw.O (c.twI w))) (D.ntw.O_inj (c.twI w))) hz
    simp only [map_mul, IsFractionRing.map, IsLocalization.map_eq] at this
    exact this
  have h3 := congrArg (ρ.e (c.twI w) (c.sd w)) h2
  rw [map_mul, hρ.e_LL0] at h3
  have hne : ρ.e (c.twI w) (c.sd w) (algebraMap _ (FractionRing (D.ntw.O (c.twI w)))
      (algebraMap (D.ntw.O0 (c.twI w)) (D.ntw.O (c.twI w)) z)) ≠ 0 :=
    (map_ne_zero _).2 ((map_ne_zero_iff _ (IsFractionRing.injective _ _)).2
      ((map_ne_zero_iff _ (D.ntw.O_inj (c.twI w))).2 hz0))
  exact mul_right_cancel₀ hne (h1.trans h3.symm)

section Point

theorem realPin_withTau {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T : Type}
    {A3 : Formalism.L2.DIV.FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
    {Rl : RealDat3 D A3 Ks} {cG : Formalism.L2.DIV.G0 Rl.Pg D.R.r ≃* G0g D.nd} {ρ : Setup D.ntw} (h : RealPin Rl cG ρ)
    (t : D.ntw.Tw) (s : Bool) (τ : ℂ ≃+* ℂ) : RealPin Rl cG (withTau ρ t s τ) :=
  { psi := h.psi, inf := h.inf, cartT := h.cartT, onbS := h.onbS, onbT := h.onbT, latS := h.latS, latT := h.latT,
    frS := h.frS, frT := h.frT, vac := h.vac, Pg := h.Pg, grp := h.grp, mu0 := h.mu0, eta := h.eta, delta := h.delta,
    deltaPl := h.deltaPl, ap := h.ap, am := h.am }

variable {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ}

theorem adapt_at (p : PtAt ex Csz) (w : D.what₂.places.Pl) (j : Fin D.R.m) (hm : More p) (ρ : Setup D.ntw) (hρ : ρ.Good)
    (hpin : RealPin p.R p.cG ρ) : ∃ ρ' : Setup D.ntw, ρ'.Good ∧ SameBut ρ ρ' ∧ Adapted p w ρ' := by
  haveI : Module.Finite (D.ntw.Ok (ex.nch.twI w) (ex.nch.k' w)) (ex.nch.Oe w) := ex.nch.Oe_fin w
  obtain ⟨g, hg⟩ := exists_ext_frac (ex.nch.Oe_inj w) (ρ.ek (ex.nch.twI w) (ex.nch.sd w) (ex.nch.k' w))
  haveI : Countable D.what₂.LL := Countable.of_equiv _ (Module.finBasis ℚ D.what₂.LL).equivFun.symm.toEquiv
  obtain ⟨τ, hτ⟩ := GlobalTheory.CompRat.exists_ringEquiv_complex_comp_eq D.what₂.LL (g.comp (ex.nch.embW w)) D.what₂.embLL
  have hfix : ∀ y : D.LL0, τ (embLL0 D y) = embLL0 D y := fun y => by
    have h := ext_onSmallField ex.nch_tie w hρ g hg y
    have h2 : τ (g (ex.nch.embW w (y : D.what₂.LL))) = D.what₂.embLL y := hτ _
    rw [h] at h2
    exact h2
  have hχ : (p.R.C.delAt (D.ntw.l (ex.nch.twI w))).ValuesIn 0 (embLL0 D) := by
    have hv := hm.2.2.small.val
    unfold CharFrame.delAt
    split_ifs
    exacts [hv.del', hv.del]
  have hδ := GlobalTheory.T.ringAut_fixing_smallField_fixes_delta_values ρ hρ (ex.nch.twI w) j (ex.nch.sd w) _ (hpin.delta _ j _) hχ τ hfix
  refine ⟨withTau ρ (ex.nch.twI w) (ex.nch.sd w) τ, withTau_good hρ _ _ τ hfix hδ, ⟨rfl, rfl, rfl, rfl, rfl⟩, realPin_withTau hpin _ _ τ,
    τ.toRingHom.comp g, fun x => hτ x, fun a => ?_⟩
  show τ (g _) = (withTau ρ (ex.nch.twI w) (ex.nch.sd w) τ).ek (ex.nch.twI w) (ex.nch.sd w) (ex.nch.k' w) _
  rw [withTau_ek, if_pos ⟨rfl, rfl⟩]
  exact congrArg τ (hg a)

end Point

end GlobalTheory.BigOn.Exp.Adapt

end
end

section

open NumberField IsDedekindDomain MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.IndefiniteRowSideFullHecke.ComponentMassSum



namespace GlobalTheory.Proof.TwistedWeightDegree

theorem degW_twist : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (V : (c.F →+* ℂ) → HSp D) (dict : ∀ σ, GA D (V σ) → Σ k, Frame ((U σ).X k).Ψ r), IsComplexData U V dict → ∀ (G₀ G : WTZ D.host.E) (s : ∀ Z : Comp Xo c, TwSec U (xiR D) Z G₀) (B : Finset ℕ) (τ : ℝ), Even G.2 → (∀ p ∈ B, p.Prime) → (∀ Z, IntOff B (s Z).lo) → (∀ Z, τ ≤ (s Z).degLo) → GoodW U (xiR D) V dict G → GoodW U (xiR D) V dict (G + G₀) ∧ rankW U (G + G₀) = rankW U G ∧ degW U (xiR D) V dict G + (rankW U G : ℝ) * (τ - logSum B) ≤ degW U (xiR D) V dict (G + G₀) := by
  intro D H Dw l Xo c r U V dict hC G₀ G s B τ hev hB hint hτ hG
  have hU : ∀ σ, GoodEmb c σ → IsUnf (U σ) := fun σ hσ => (hC.2 σ hσ).1
  have hA : ∀ G' : WTZ D.host.E, Adds U V dict G' := fun G' =>
    GlobalTheory.T.component_ranks_degrees_add_with_masses D H Dw l Xo c r U V dict G' (GlobalTheory.T.cuspForms_supLattice_split_over_components D H Dw l Xo c r U V dict hU G')
      ((GlobalTheory.T.components_peterssonOrthogonal_and_masses D H Dw l Xo c r U V dict hC G').1)
  have hOn : ∀ Z, GoodOn U (xiR D) V dict Z G := (hA G).1.1 hG
  have hgr : ∀ Z, GoodOn U (xiR D) V dict Z (G + G₀) ∧ rankOn U Z (G + G₀) = rankOn U Z G := fun Z =>
    GlobalTheory.T.twistingSection_preserves_hermitianLattices_ranks D.host.E H Dw l Xo c r U (xiR D) D V dict Z G₀ (s Z) G hU hev (hOn Z)
  have hG' : GoodW U (xiR D) V dict (G + G₀) := (hA (G + G₀)).1.2 (fun Z => (hgr Z).1)
  obtain ⟨-, hr1, -, -, hd1⟩ := (hA G).2 hG
  obtain ⟨-, hr2, -, -, hd2⟩ := (hA (G + G₀)).2 hG'
  have hrank : rankW U (G + G₀) = rankW U G := by
    rw [hr1, hr2]; exact finsum_congr fun Z => (hgr Z).2
  refine ⟨hG', hrank, ?_⟩
  haveI : Finite (Comp Xo c) := finite_comp
  letI := Fintype.ofFinite (Comp Xo c)
  have hZ : ∀ Z, degOn U (xiR D) V dict Z G + (rankOn U Z G : ℝ) * (τ - logSum B) ≤
      degOn U (xiR D) V dict Z (G + G₀) := fun Z => by
    have h1 := GlobalTheory.T.cuspForm_supLattice_degree_twist_lower_bound D.host.E H Dw l Xo c r U (xiR D) D V dict Z G₀ (s Z) G B hU hev hB (hint Z) (hOn Z)
    have h2 : (rankOn U Z G : ℝ) * (τ - logSum B) ≤ (rankOn U Z G : ℝ) * ((s Z).degLo - logSum B) :=
      mul_le_mul_of_nonneg_left (by linarith [hτ Z]) (Nat.cast_nonneg _)
    linarith
  rw [hd1, hd2, hr1]
  simp only [finsum_eq_sum_of_fintype, Nat.cast_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro Z _
  rw [(hgr Z).2]
  linarith [hZ Z]

end GlobalTheory.Proof.TwistedWeightDegree
end
