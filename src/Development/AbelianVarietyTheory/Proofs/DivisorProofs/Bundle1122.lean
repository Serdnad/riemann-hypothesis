module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle589
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle807
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle626
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle009
public import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
public import Formalism.LocalToGlobal.Divisibility.ProjLemmas
public import Formalism.LocalToGlobal.Divisibility.RowLatLemmas
public import Formalism.LocalToGlobal.IndefiniteReal.CxLemmas
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle013
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle003
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle230
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1092
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.EffectiveEpi.Comp
import Mathlib.CategoryTheory.ExtremalEpi
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle029
import Development.AbelianVarietyTheory.Definitions.Divisors.IsFrameOfForallExists
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle032
import Development.AbelianVarietyTheory.PublishedTheorems.BesselIntegrals.ExistsLinearIndependentNormLe
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Published
open scoped CategoryTheory.Obj
open MonObj
open scoped CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.TorusFibre

open GlobalTheory.SplitTorus (torusMap bcIso)

set_option synthInstance.maxHeartbeats 200000 in
theorem isClosedImmersion_special_of_local : ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (K : Type) [Field K] [Algebra R K]
    (G : Over (Spec (CommRingCat.of R))) [GrpObj G], IsSemiAbelian G →
    ∀ (r : ℕ) (u : GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraMaps.torus R r ⟶ G), IsMonHom u →
    Mono ((GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraMaps.baseChange R K).map u) →
    IsClosedImmersion ((GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraMaps.baseChange R (IsLocalRing.ResidueField R)).map u).left := by
  intro R _ _ _ K _ _ G _ hG r u hu hmono
  let k := IsLocalRing.ResidueField R
  let Ω := AlgebraicClosure k
  refine GlobalTheory.T.closedImmersion_of_baseChange_field_ext R k Ω (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraMaps.torus R r) G u ?_
  let p : Spec (CommRingCat.of Ω) ⟶ Spec (CommRingCat.of R) :=
    Spec.map (CommRingCat.ofHom (algebraMap R Ω))
  obtain ⟨E⟩ := hG.fibres Ω p
  let v := (bcIso p (Fin r → ℤ)).hom ≫ (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraMaps.baseChange R Ω).map u
  have hv : IsClosedImmersion v.left := by
    refine GlobalTheory.T.isClosedImmersion_splitTorus_into_torusExtension Ω _ E r v inferInstance fun q hq φ hφ h => hφ ?_
    have hsep : IsSeparated G.hom := hG.separated
    have e1 : torusMap _ φ ≫ (bcIso p (Fin r → ℤ)).hom =
        (bcIso p (ZMod q)).hom ≫ (Over.pullback p).map (torusMap _ φ) :=
      (GlobalTheory.SplitTorus.comm_bcMap_iff p _ _).1 (GlobalTheory.SplitTorus.torusMap_bcMap p φ)

    have hΩ : (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraMaps.baseChange R Ω).map (torusMap _ φ ≫ u) =
        (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraMaps.baseChange R Ω).map 1 := by
      rw [Functor.map_comp, Functor.map_one, ← cancel_epi (bcIso p (ZMod q)).hom, MonObj.comp_one,
        ← Category.assoc]
      change ((bcIso p (ZMod q)).hom ≫ (Over.pullback p).map (torusMap _ φ)) ≫ _ = _
      rw [← e1, Category.assoc]
      exact h

    have hk := GlobalTheory.T.overSpecBaseChange_map_eq_of_fieldExtension R k Ω _ _ _ _ hΩ
    have hf : torusMap _ φ ≫ u = 1 :=
      GlobalTheory.T.splitTorus_hom_ext_of_eq_mod_maximalIdeal_pow R (ZMod q) G hsep _ _ (GlobalTheory.T.splitTorus_hom_pullback_quotient_pow_eq_one R (ZMod q) G _ inferInstance hk)

    let pK : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of R) :=
      Spec.map (CommRingCat.ofHom (algebraMap R K))
    have hK' : (Over.pullback pK).map (torusMap _ φ) = (Over.pullback pK).map (torusMap _ 0) := by
      rw [← cancel_mono ((GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraMaps.baseChange R K).map u)]
      change (Over.pullback pK).map (torusMap _ φ) ≫ (Over.pullback pK).map u =
        (Over.pullback pK).map (torusMap _ 0) ≫ (Over.pullback pK).map u
      rw [← Functor.map_comp, ← Functor.map_comp, hf, GlobalTheory.SplitTorus.torusMap_zero, MonObj.one_comp]
    rw [GlobalTheory.SplitTorus.pullback_map_torusMap, GlobalTheory.SplitTorus.pullback_map_torusMap,
      cancel_epi, cancel_mono] at hK'
    exact GlobalTheory.SplitTorus.torusMap_injective hK'
  have : (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraMaps.baseChange R Ω).map u = (bcIso p (Fin r → ℤ)).inv ≫ v := by
    simp [v]
  rw [this, Over.comp_left]
  haveI : IsIso (bcIso p (Fin r → ℤ)).inv.left :=
    inferInstanceAs (IsIso ((Over.forget _).map (bcIso p (Fin r → ℤ)).inv))
  exact IsClosedImmersion.comp _ _

end GlobalTheory.TorusFibre
end
end

section

noncomputable section

open Module NumberField
open Formalism.DivisionValues Formalism.L2.Indef Formalism.L2.DIV Formalism.IndefR.Cx

namespace GlobalTheory.OneForm

section GroupAlgebra

variable {K : Type} [Field K] [CharZero K] {G : Type} [Group G] [Fintype G]


open Classical in
def typeSum (P : Subgroup G) (ψ : P →* Kˣ) (χ : G → K) : K := ∑ h : P, χ (h : G) * (((ψ h)⁻¹ : Kˣ) : K)

end GroupAlgebra

section Modules

variable {K : Type} [Field K] [CharZero K] {G : Type} [Group G] [Fintype G]
  {V : Type} [AddCommGroup V] [Module K V]

omit [CharZero K] in
theorem asAlg_eq_sum (r : Representation K G V) (a : MonoidAlgebra K G) (x : V) :
    r.asAlgebraHom a x = ∑ g : G, a.coeff g • r g x := by
  conv_lhs => rw [eq_sum_single a]

  simp [map_sum, LinearMap.sum_apply]



end Modules

section Coordinates

variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem range_toF {G : Type} [Group G] [Fintype G] {Pl0 : Type} (B : BlockDat K G Pl0) (ℓ : Lvl K G)
    (Z : Submodule K B.S.Forms) :
    LinearMap.range (B.toF ℓ Z) = Z ⊓ LinearMap.range (B.r.asAlgebraHom (goodAt ℓ.X ℓ.P ℓ.ψ)) := by
  have hop : ∀ (a : MonoidAlgebra K G) (φ : B.S.Forms), B.S.gaOp B.r a φ = B.r.asAlgebraHom a φ := by
    intro a φ
    rw [asAlg_eq_sum, CSD.gaOp, LinearMap.sum_apply]
    rfl
  have hV : LinearMap.range (B.vE ℓ).mulVecLin =
      LinearMap.range (B.S.gaMat B.r (goodAt ℓ.X ℓ.P ℓ.ψ)).mulVecLin :=
    (image_idempotent_spec K B.S.dim (B.S.gaMat B.r (goodAt ℓ.X ℓ.P ℓ.ψ))).2
  ext φ
  constructor
  · rintro ⟨y, rfl⟩
    refine ⟨(B.mem_goodPart_iff ℓ Z _).1 (B.zE_mem ℓ Z y), ?_⟩
    have : (B.vE ℓ).mulVec ((B.zE ℓ Z).mulVec y) ∈ LinearMap.range (B.vE ℓ).mulVecLin := ⟨_, rfl⟩
    rw [hV] at this
    obtain ⟨u, hu⟩ := this
    refine ⟨B.S.basis.equivFun.symm u, ?_⟩
    rw [B.toF_apply, ← hu, ← hop, LinearEquiv.eq_symm_apply, ← CSD.gaMat_mulVec_equivFun,
      LinearEquiv.apply_symm_apply]
    rfl
  · rintro ⟨hZ, w, hw⟩
    have : B.S.basis.equivFun φ ∈ LinearMap.range (B.vE ℓ).mulVecLin := by
      rw [hV]
      refine ⟨B.S.basis.equivFun w, ?_⟩
      rw [Matrix.mulVecLin_apply, CSD.gaMat_mulVec_equivFun, hop, hw]
    obtain ⟨u, hu⟩ := this
    rw [Matrix.mulVecLin_apply] at hu
    have hu0 : u ∈ B.Z0 ℓ Z := by
      rw [BlockDat.Z0, B.mem_goodPart_iff, hu, LinearEquiv.symm_apply_apply]
      exact hZ
    obtain ⟨y, hy⟩ := B.exists_zE ℓ Z hu0
    exact ⟨y, by rw [B.toF_apply, hy, hu, LinearEquiv.symm_apply_apply]⟩

variable {Bs : DefBase K} {A : DefAmb Bs} (X : CxData A) {fc : DefSub A → DefFace Bs} (cr : Crd A fc) (b : Bool)

theorem iC_cpt (t : Bs.Tup) (x : Fin ((lv (fc X.zs) b).dQ t) → K) :
    X.iC cr b t (cpt Bs.v0.embedding x) = X.Θ t (X.jR t (cr.toR X.zs b t x)) := by
  classical
  conv_rhs => rw [← Finset.univ_sum_single x]

  rw [CxData.iC, lin_apply, map_sum, map_sum, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have : (Pi.single k (x k) : Fin _ → K) = x k • Pi.single k 1 := by
    funext i; by_cases hi : i = k <;> simp [hi]
  rw [this, map_smul, map_smulₛₗ, map_smul]
  rfl

end Coordinates

section Family

variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {m : ℕ}
  {A : FamIn K G Pl0 T m}

def OneVector (X : Finset (G → K)) (P : Subgroup G) (ψ : P →* Kˣ) : Prop :=
  ∀ χ ∈ X, typeSum P ψ χ = (Nat.card P : K)

section Faces

variable (X : CxData A.fam.amb) (P0 : Subgroup G) (ψ0 : P0 →* Kˣ) (P1 : Subgroup G) (ψ1 : P1 →* Kˣ)
  (Dc : ∀ Zs : DefSub A.fam.amb, DefCols (A.side P1 ψ1 Zs)) (Sp : ∀ Zs : DefSub A.fam.amb, SPer (Dc Zs))
  (Zsc : DefSub A.fam.amb → IndefScale A.fam.base)

end Faces

end Family

section Concrete

open Formalism.BasicNotions Formalism.IndefR.Links
attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

def rowSub (R : RealDat D A Ks) (t : T) : Submodule D.what₂.LL (A.fam.amb.FR t) :=
  (LinearMap.range (LinearMap.adjoint (Tw.map (twAt D.what₂.embLL A.v0) (R.Th t)))).comap
    (Tw.semi (σ' := A.v0.embedding) (twAt D.what₂.embLL A.v0) R.emb0 (R.jX t))

def GoodInduced (R : RealDat D A Ks) : Prop :=
  ∀ χ ∈ A.X, GlobalTheory.IndefiniteRowSideFullHecke.CuspidalInducedCharacter.IsCuspIndProdChar R.Pg D.R.r D.what₂.embLL fun g => χ (R.eG.symm g)

theorem oneVector_of_whittaker (R : RealDat D A Ks) (F : Face D A) (hW : GlobalTheory.IndefiniteRowSideFullHecke.CuspidalInducedCharacter.OneWhittakerVector)
    (hlev : R.grp_levels F) (hind : GoodInduced R) : OneVector A.X F.P0 F.ψ0 := by
  classical
  obtain ⟨ψ, hψ, hP, -⟩ := hlev
  intro χ hχ
  have h := hW D.host.E R.Pg D.R.r ℂ (RingHom.id ℂ) ψ hψ (fun g => D.what₂.embLL (χ (R.eG.symm g))) (hind χ hχ)
  rw [← hP] at h
  let e : (R.levR F false).H ≃ F.P0 := R.eG.symm.toEquiv.subtypeEquiv fun _ => Iff.rfl
  apply D.what₂.embLL.injective

  rw [map_natCast, ← Nat.card_congr e, ← h, typeSum, map_sum]
  unfold GlobalTheory.IndefiniteRowSideFullHecke.CuspidalInducedCharacter.lvlSum
  letI := GlobalTheory.IndefiniteRowSideFullHecke.CuspidalInducedCharacter.fintypeH (R.levR F false)
  refine (Fintype.sum_equiv e _ _ fun x => ?_).symm
  rw [map_mul]
  rfl

end Concrete

end GlobalTheory.OneForm
end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult
open Formalism.L2.Host (HChar ordF atFin IsUnitAt)
open GlobalTheory.IndefiniteRowSideFullHecke
open scoped TensorProduct InnerProductSpace

namespace GlobalTheory.AdelicLiftCompare

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem chrEq_mul {c c' : (AE D)ˣ →* Circle} {χ χ' : HChar D.host.E} (h : ChrEq c χ) (h' : ChrEq c' χ') :
    ChrEq (c * c') (χ * χ') := by
  refine ⟨⟨h.1.1.mul h'.1.1, fun x => ?_⟩, fun P e he k x hx => ?_⟩
  · rw [MonoidHom.mul_apply, h.1.2, h'.1.2, one_mul]
  · rw [MonoidHom.mul_apply, Circle.coe_mul, h.2 P e he k x hx, h'.2 P e he k x hx, ← Units.val_mul]
    rfl

section Places

variable {T : Type} {L : LevCh D T} {μ0 : T} (hL : L.Is μ0)
include hL

end Places

section Generic

variable {G H W : Type} [Group G] [Group H] [NormedAddCommGroup W] [InnerProductSpace ℂ W] (π : G →* H) (ρ : G →* Module.End ℂ W)

end Generic

section Forms

variable {V : HSp D} (c : CoefA V) (hc : c.Is) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank)

include hc

end Forms

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)

def IsResidual (i : Fin D.R.m) (t : T) (s : ℂ →+* ℂ) (m : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) : Prop :=
  (∀ PP ∈ R.Pg, m PP = (LiftFormsMainTerm.conjRes s (R.chi ((i : ℕ) + 1)) PP)⁻¹) ∧ ∀ PP ∈ R.Q t, m PP = LiftFormsMainTerm.conjRes s (R.xiR t) PP

variable {R}

section Residual

variable {i : Fin D.R.m} {t : T} {s : ℂ →+* ℂ} {m : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ} (hm : IsResidual R i t s m)
  (P : LevelP R.Pg D.R.r ℂ)

include hm

end Residual

variable (R)

variable {R} {F : Face D A}

end GlobalTheory.AdelicLiftCompare

end
end

section

namespace GlobalTheory.HookDiagram

theorem hookProd_eq_of_mem (μ : YoungDiagram) (n : ℕ) (a : ℕ → ℕ)
    (h : ∀ i j, (i, j) ∈ μ ↔ i < n ∧ j < a i) :
    Formalism.LatticeIndexTer.hookProd μ = GlobalTheory.IndefiniteRowSideFullHecke.SchurTensorLattices.hookProd n a := by
  have hrow : ∀ r, r < n → μ.rowLen r = a r := by
    intro r hr
    apply le_antisymm
    · by_contra hlt
      rw [not_le] at hlt
      have hm : (r, a r) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr hlt
      exact lt_irrefl _ ((h r (a r)).mp hm).2
    · by_contra hlt
      rw [not_le] at hlt
      have hm : (r, μ.rowLen r) ∈ μ := (h r _).mpr ⟨hr, hlt⟩
      exact lt_irrefl _ (YoungDiagram.mem_iff_lt_rowLen.mp hm)
  have hcol : ∀ r c, Finset.filter (fun r' => c < a r') (Finset.Ioo r n) =
      Finset.Ioo r (μ.colLen c) := by
    intro r c
    ext r'
    simp only [Finset.mem_filter, Finset.mem_Ioo]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨h1, YoungDiagram.mem_iff_lt_colLen.mp ((h r' c).mpr ⟨h2, h3⟩)⟩
    · rintro ⟨h1, h2⟩
      have hm := (h r' c).mp (YoungDiagram.mem_iff_lt_colLen.mpr h2)
      exact ⟨⟨h1, hm.1⟩, hm.2⟩
  have hrc : ∀ r c, r < n → c < a r → r < μ.colLen c := fun r c hr hc =>
    YoungDiagram.mem_iff_lt_colLen.mp ((h r c).mpr ⟨hr, hc⟩)
  unfold Formalism.LatticeIndexTer.hookProd GlobalTheory.IndefiniteRowSideFullHecke.SchurTensorLattices.hookProd
  rw [Finset.prod_finset_product μ.cells (Finset.range n) (fun r => Finset.range (a r))]
  · apply Finset.prod_congr rfl
    intro r hr
    rw [Finset.mem_range] at hr
    apply Finset.prod_congr rfl
    intro c hc
    rw [Finset.mem_range] at hc
    dsimp only
    rw [hcol r c, Nat.card_Ioo, hrow r hr]
    have := hrc r c hr hc
    omega
  · rintro ⟨i, j⟩
    simp only [YoungDiagram.mem_cells, Finset.mem_range]
    exact h i j

theorem hookOf_eq (n : ℕ) (a : ℕ → ℕ) (ha : ∀ x y, x ≤ y → y < n → a y ≤ a x) :
    GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.hookOf n a = GlobalTheory.IndefiniteRowSideFullHecke.SchurTensorLattices.hookProd n a := by
  have hsort : ((List.range n).map a).Pairwise (· ≥ ·) := by
    rw [List.pairwise_map]
    exact List.pairwise_lt_range.imp_of_mem
      (fun {x y} _ hy hxy => ha x y hxy.le (List.mem_range.mp hy))
  have hL : ((List.range n).map a).insertionSort (· ≥ ·) = (List.range n).map a :=
    hsort.insertionSort_eq
  unfold GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.hookOf
  apply hookProd_eq_of_mem
  intro i j
  rw [YoungDiagram.mem_ofRowLens]
  simp only [hL, List.length_map, List.length_range, List.getElem_map, List.getElem_range,
    exists_prop]

theorem hookOf_pos_log (n : ℕ) (a : ℕ → ℕ) (ha : ∀ x y, x ≤ y → y < n → a y ≤ a x) :
    0 < GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.hookOf n a ∧
      Real.log (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.hookOf n a : ℝ) = Formalism.BasicNotions.DV.logHook n (fun k => (a k : ℝ)) := by
  rw [hookOf_eq n a ha]
  have hm := GlobalTheory.LiftSizeCompare.hookProd_mul n a ha
  have hinner : ∀ r ∈ Finset.range n,
      0 < ∏ l ∈ Finset.Ioo r n, (a r - a l + (l - r)) := by
    intro r _
    apply Finset.prod_pos
    intro l hl
    rw [Finset.mem_Ioo] at hl
    omega
  have hPpos : 0 < ∏ r ∈ Finset.range n, ∏ l ∈ Finset.Ioo r n, (a r - a l + (l - r)) :=
    Finset.prod_pos hinner
  have hHpos : 0 < GlobalTheory.IndefiniteRowSideFullHecke.SchurTensorLattices.hookProd n a := by
    rcases Nat.eq_zero_or_pos (GlobalTheory.IndefiniteRowSideFullHecke.SchurTensorLattices.hookProd n a) with h0 | h0
    · have hF : 0 < ∏ r ∈ Finset.range n, (a r + n - 1 - r).factorial :=
        Finset.prod_pos fun r _ => Nat.factorial_pos _
      rw [h0, zero_mul] at hm
      omega
    · exact h0
  refine ⟨hHpos, ?_⟩
  have hmR : (GlobalTheory.IndefiniteRowSideFullHecke.SchurTensorLattices.hookProd n a : ℝ) =
      ((∏ r ∈ Finset.range n, (a r + n - 1 - r).factorial : ℕ) : ℝ) /
        ((∏ r ∈ Finset.range n, ∏ l ∈ Finset.Ioo r n, (a r - a l + (l - r)) : ℕ) : ℝ) := by
    rw [eq_div_iff (by exact_mod_cast hPpos.ne'), ← Nat.cast_mul, hm]
  have hFpos : (0 : ℝ) < ((∏ r ∈ Finset.range n, (a r + n - 1 - r).factorial : ℕ) : ℝ) := by
    exact_mod_cast Finset.prod_pos fun r _ => Nat.factorial_pos _
  rw [hmR, Real.log_div hFpos.ne' (by exact_mod_cast hPpos.ne')]
  unfold Formalism.BasicNotions.DV.logHook
  congr 1
  · rw [Nat.cast_prod, Real.log_prod]
    · apply Finset.sum_congr rfl
      intro r hr
      rw [Finset.mem_range] at hr
      have hg : (a r : ℝ) + n - r = ((a r + n - 1 - r : ℕ) : ℝ) + 1 := by
        rw [Nat.cast_sub (show r ≤ a r + n - 1 by omega), Nat.cast_sub (show 1 ≤ a r + n by omega)]
        push_cast
        ring
      rw [hg, Real.Gamma_nat_eq_factorial]
    · intro r _
      exact_mod_cast (Nat.factorial_pos _).ne'
  · rw [Nat.cast_prod, Real.log_prod]
    · apply Finset.sum_congr rfl
      intro r hr
      rw [Nat.cast_prod, Real.log_prod]
      · apply Finset.sum_congr rfl
        intro l hl
        rw [Finset.mem_Ioo] at hl
        have hal : a l ≤ a r := ha r l hl.1.le hl.2
        congr 1
        rw [Nat.cast_add, Nat.cast_sub hal, Nat.cast_sub hl.1.le]
        ring
      · intro l hl
        rw [Finset.mem_Ioo] at hl
        have hpos : 0 < a r - a l + (l - r) := by omega
        exact_mod_cast hpos.ne'
    · intro r hr
      exact_mod_cast (hinner r hr).ne'

end GlobalTheory.HookDiagram
end

section

open CategoryTheory AlgebraicGeometry NumberField MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory CategoryTheory.Hom.group

theorem _root_.GlobalTheory.T.degree_le_of_pullback_le_pow_finiteEtale : ∀ (k : Type) [Field k] (X : Scheme.{0}) [IsIntegral X] (f : X ⟶ Spec (CommRingCat.of k)) (g : ℕ), SmoothOfRelativeDimension g f → ∀ (H : LB X) (m : ℕ) (s : Fin (m + 1) → LB.Sec H), H.IsLB → GlobalTheory.AbLaw.VeryAmpleBy f H s → ∃ C : ℕ, ∀ (φ : X ⟶ X) [IsFinite φ] [Etale φ], φ ≫ f = f → ∀ (D q : ℕ), 1 ≤ q → (∀ x, φ.finrank x = D) → (∃ (σ : LB.Sec (LB.div (GlobalTheory.AbLaw.pw H (q : ℤ)) (H.pull φ))) (j : (LB.div (GlobalTheory.AbLaw.pw H (q : ℤ)) (H.pull φ)).ι), σ.f j ≠ 0) → D ≤ C * q ^ g := by
  first | exact @GlobalTheory.degree_le_of_pull_le_pow | exact GlobalTheory.degree_le_of_pull_le_pow | (intros; apply GlobalTheory.degree_le_of_pull_le_pow <;> assumption)
end
