module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle029
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle033
import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleWeightMiddleEntries
import Formalism.LocalToGlobal.Columns.RowFormsGood
import Formalism.LocalToGlobal.Columns.Bundle033
import Formalism.LocalToGlobal.Columns.ToHLatLemmas
import Formalism.LocalToGlobal.Divisibility.ClassSumLemmas
import Formalism.LocalToGlobal.Divisibility.ProjLemmas
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.AuxStatement14
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.ClassSumDualGeOfFamily
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle021
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.GoodPartEq
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle463
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DeepElementConjRationalAtBadPrime
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle499

@[expose] public section

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.Db GlobalTheory.Mem.Top.Bl.WitTr NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Top.Bl.WitTr

open Formalism.L2.Geo
open Formalism.L2.Geo.PadPkg renaming md → padMd
open Formalism.L2.Geo.CompatiblePlaces' renaming md → tiedMd

open DivX (md) in
@[reducible] def divXTr {B : Base} {f : Fr B.toPre} {T : TwDat B}
    (w : ColW B f T) (Z : w.Lt) (N : ∀ u, Submodule (𝓞 B.LL) (Z.V.div.Nu u).V)
    (h : B.Word → ℝ) (Y : DivX (w.D Z)) : DivX (w.D (setDivZ Z N h)) :=
  { Y with md := fun S κ p _ la z => { md Y S κ p la z with } }

namespace GeoDivTr

variable {B : Base} {f : Fr B.toPre} {T : TwDat B}
variable (col : ColW B f T) (Z : col.Lt)
variable (N : ∀ u, Submodule (𝓞 B.LL) (Z.V.div.Nu u).V) (h : B.Word → ℝ)

local notation "D₀" => col.D Z
local notation "D₁" => col.D (setDivZ Z N h)



@[reducible] def datBk {Lev : Type} (w : Dat D₁ Lev) : Dat D₀ Lev := { w with }



@[reducible] def mdlT {p : ℕ} [Fact p.Prime] {M : ℕ} {rk : DV.Emb D₀ p → ℕ} (m : DV.Mdl D₀ p M rk) : DV.Mdl D₁ p M rk := { m with }



@[reducible] def locT {M j p : ℕ} (l : ModuliIntegralCharts.Loc D₀ M j p) : ModuliIntegralCharts.Loc D₁ M j p := { l with }



@[reducible] def padT {M j : ℕ} {Comp : Type} {jC : ∀ (p : ℕ) [Fact p.Prime], PlL D₀ p → (DV.KW p →+* ℂ)} {ng : NgPkg}
    (P : PadPkg D₀ M j Comp jC ng) : PadPkg D₁ M j Comp jC ng :=
  { P with
    loc := fun p => locT col Z N h (P.loc p)
    ex := fun p => { P.ex p with }
    locB := fun p hp => { P.locB p hp with }
    pbKF := fun p _ k => P.pbKF p k
    bc := fun p z => P.bc p z
    md := fun p _ la z => mdlT col Z N h (padMd P p la z) }



@[reducible] def shimUT {G : DV.Geo (D₀).what₂.LL} {Lev : Type} {jC : ∀ (p : ℕ) [Fact p.Prime], PlL D₀ p → (DV.KW p →+* ℂ)} {ng : NgPkg}
    {w : Dat D₁ Lev} (U : ShimU D₀ G jC ng (datBk col Z N h w)) : ShimU D₁ G jC ng w :=
  { U with alg := { U.alg with }, pad := padT col Z N h U.pad }

@[reducible] def wtB {j : ℕ} (w : WeightFamilies.Wt D₁ j) : WeightFamilies.Wt D₀ j := { w with }



@[reducible] def formsT {G : DV.Geo (D₀).what₂.LL} {NW : ℕ → ℕ} {CompW : ℕ → Type} [∀ j, Fintype (CompW j)]
    {algW : ∀ j, AlgPkg G (D₀).what₂.Tau (NW j) (CompW j)} {PtY : ℕ → ℕ → Type}
    (P : FormsPkg D₀ G NW CompW algW PtY) :
    FormsPkg D₁ G NW CompW (fun j => { algW j with }) PtY where
  KO := P.KO
  fKO := P.fKO
  nfKO := P.nfKO
  eO := P.eO
  kL := P.kL
  kL_eO := P.kL_eO
  Cusp := fun j w => P.Cusp j (wtB col Z N h w)
  acgC := fun j w => P.acgC j (wtB col Z N h w)
  modC := fun j w => P.modC j (wtB col Z N h w)
  fdC := fun j w => P.fdC j (wtB col Z N h w)
  modOC := fun j w => P.modOC j (wtB col Z N h w)
  towC := fun j w => P.towC j (wtB col Z N h w)
  cmp := fun j w c => P.cmp j (wtB col Z N h w) c
  cmp_mem := fun j w c F => P.cmp_mem j (wtB col Z N h w) c F
  cmp_cusp := fun j w c F => P.cmp_cusp j (wtB col Z N h w) c F
  cmp_span := fun j h1 h2 w s hs => P.cmp_span j h1 h2 (wtB col Z N h w) s hs
  cmp_indep := fun j w _ v hv => P.cmp_indep j (wtB col Z N h w) v hv
  mulC := fun j w w' F F' => P.mulC j (wtB col Z N h w) (wtB col Z N h w') F F'
  cmp_mul := fun j w w' c F F' => P.cmp_mul j (wtB col Z N h w) (wtB col Z N h w') c F F'
  supN := fun j w => P.supN j (wtB col Z N h w)
  supN_nonneg := fun j w => P.supN_nonneg j (wtB col Z N h w)
  supN_eq_zero := fun j w => P.supN_eq_zero j (wtB col Z N h w)
  supN_smul := fun j w => P.supN_smul j (wtB col Z N h w)
  supN_add := fun j w => P.supN_add j (wtB col Z N h w)
  l2NormAlt := fun j w => P.l2NormAlt j (wtB col Z N h w)
  l2Norm_nonneg_bis := fun j w => P.l2Norm_nonneg_bis j (wtB col Z N h w)
  l2Norm_eq_zero_iff := fun j w => P.l2Norm_eq_zero_iff j (wtB col Z N h w)
  l2Norm_smul_alt := fun j w => P.l2Norm_smul_alt j (wtB col Z N h w)
  l2Norm_add_le' := fun j w => P.l2Norm_add_le' j (wtB col Z N h w)
  l2Norm_le_supNorm_alt := fun j w => P.l2Norm_le_supNorm_alt j (wtB col Z N h w)
  Cu := P.Cu
  Xc := P.Xc
  Xc_lat := P.Xc_lat
  FJt := fun j c χ w => P.FJt j c χ (wtB col Z N h w)
  acgF := fun j c χ w => P.acgF j c χ (wtB col Z N h w)
  modF := fun j c χ w => P.modF j c χ (wtB col Z N h w)
  sg := fun j c χ w => P.sg j c χ (wtB col Z N h w)
  Pt := P.Pt
  pt66 := P.pt66
  vAtC := fun j la y w => P.vAtC j la y (wtB col Z N h w)
  vAtC_zero := fun j la y w => P.vAtC_zero j la y (wtB col Z N h w)
  vAtC_ne_bot := fun j la y w => P.vAtC_ne_bot j la y (wtB col Z N h w)
  vAtC_add := fun j la y w => P.vAtC_add j la y (wtB col Z N h w)
  vAtC_smul := fun j la y w => P.vAtC_smul j la y (wtB col Z N h w)
  vAtC_mul := fun j la y w w' => P.vAtC_mul j la y (wtB col Z N h w) (wtB col Z N h w')
  thAll := fun j w => P.thAll j (wtB col Z N h w)
  shortTh := fun j w => P.shortTh j (wtB col Z N h w)



def famT {G : DV.Geo (D₀).what₂.LL} {Lev : Type} (F : ShimFam D₀ G Lev) : ShimFam D₁ G Lev :=
  { F with
    U := fun w => shimUT col Z N h (F.U (datBk col Z N h w))
    forms := formsT col Z N h F.forms }



theorem heq_mdlT {p : ℕ} [Fact p.Prime] {A A' : Type} {M M' : ℕ} {rk rk' : DV.Emb D₀ p → ℕ}
    (f : A → DV.Mdl D₀ p M rk) (g : A' → DV.Mdl D₀ p M' rk') (hA : A = A') (hM : M = M') (hrk : rk = rk')
    (hfg : HEq f g) : HEq (fun z => mdlT col Z N h (f z)) (fun z => mdlT col Z N h (g z)) := by
  subst hA hM hrk
  obtain rfl := eq_of_heq hfg
  rfl



theorem geoTiedP_divTr {X : DivX D₀} {inK : X.Lev → ℕ → Prop} (hg : GeoTiedP X inK) :
    GeoTiedP (divXTr col Z N h X) inK := by
  obtain ⟨F, ePl, eC, hT, hJ, hC, hI, hL⟩ := hg
  refine ⟨famT col Z N h F, ePl, eC, ⟨⟨hT.shv.lev, fun w hw => hT.shv.shv (datBk col Z N h w) hw⟩,
    ⟨hT.pl.wt, hT.pl.jc, fun w hw => hT.pl.mp (datBk col Z N h w) hw, ?_, fun w hw => hT.pl.curveM (datBk col Z N h w) hw,
      fun w hw => hT.pl.degM (datBk col Z N h w) hw, fun w hw => hT.pl.htMdl (datBk col Z N h w) hw,
      fun w hw => hT.pl.htCurve (datBk col Z N h w) hw⟩, ⟨fun j h1 h2 c => hT.geo.yv j h1 h2 c, fun j h1 h2 c => hT.geo.ybd j h1 h2 c,
      fun j h1 h2 c la => hT.geo.lw j h1 h2 c la⟩, hT.lev_κg⟩, hJ, hC,
    fun w w' hs hk hj hw hw' => hI (datBk col Z N h w) (datBk col Z N h w') hs hk hj hw hw', fun w M => hL (datBk col Z N h w) M⟩
  intro w hw p _ la
  have hS := hT.shv.shv (datBk col Z N h w) hw
  have hM : (X.shv w.S w.κ).N = (datBk col Z N h w).N := by rw [show w.S = (datBk col Z N h w).S from rfl, show w.κ = (datBk col Z N h w).κ from rfl, hS]; rfl
  have hj : (X.shv w.S w.κ).j = (datBk col Z N h w).j := by rw [show w.S = (datBk col Z N h w).S from rfl, show w.κ = (datBk col Z N h w).κ from rfl, hS]; rfl
  have hrk : DV.rkOf (DV.PsiOf D₀ (X.jC p la)) (X.shv w.S w.κ).N (X.shv w.S w.κ).j =
      DV.rkOf (DV.PsiOf D₀ (F.jC p (ePl p la))) (datBk col Z N h w).N (datBk col Z N h w).j := by
    rw [hT.pl.jc p la, hM, hj]
  exact heq_mdlT col Z N h _ _ (hT.pl.mp (datBk col Z N h w) hw p la) hM hrk (tiedMd hT.pl (datBk col Z N h w) hw p la)

end GeoDivTr

open GeoDivTr


theorem divT_setDiv : ∀ {B : Base} {f : Fr B.toPre} {T : TwDat B} (w : ColW B f T)
    (Z : w.Lt) {Wt : Set B.places.Pl} {nch : NChoice (w.D Z)} (n : NchT w Z Wt nch)
    (Y : DivX (w.D Z)) (N : ∀ u, Submodule (𝓞 B.LL) (Z.V.div.Nu u).V) (h : B.Word → ℝ),
    DivT n Y →
    let n' : NchT w (setDivZ Z N h) Wt { nch with } :=
      { n with tp := { n.tp with }, tie := { n.tie with }, chrPsi := n.chrPsi }
    Nonempty (DivT n' (divXTr w Z N h Y)) := by
  intro B f T w Z Wt nch n Y N h d
  refine ⟨{
    Qp := d.Qp
    chr := { d.chr with }
    loc := ?_
    inK := d.inK
    geo := geoTiedP_divTr w Z N h d.geo }⟩
  obtain ⟨h1, h2⟩ := d.loc
  exact ⟨h1, { h2 with }⟩

end GlobalTheory.Mem.Top.Bl.WitTr

end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

namespace GlobalTheory.Mem.R3.Rw.Mats

section Gen

variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G]


omit [NumberField K] in
theorem isConjAt_mk {σ : K →+* ℂ} (hσ : ∀ a, σ (star a) = starRingEnd ℂ (σ a)) :
    Formalism.DivisionValues.IsConjAt (InfinitePlace.mk σ) := fun a => by
  rcases InfinitePlace.embedding_mk_eq σ with e | e
  · rw [e]
    exact hσ a
  · rw [e, ComplexEmbedding.conjugate_coe_eq, ComplexEmbedding.conjugate_coe_eq, hσ a]


omit [NumberField K] [StarRing K] in
theorem posDef_of_mk {n : ℕ} {σ : K →+* ℂ} {H : Matrix (Fin n) (Fin n) K}
    (h : (H.map (InfinitePlace.mk σ).embedding).PosDef) : (H.map σ).PosDef := by
  rcases InfinitePlace.embedding_mk_eq σ with e | e
  · rwa [e] at h
  · rw [e] at h
    have h1 := h.isHermitian
    have e2 : H.map σ = (H.map (ComplexEmbedding.conjugate σ))ᵀ := by
      ext i j
      have := h1.apply j i
      simp only [Matrix.map_apply, ComplexEmbedding.conjugate_coe_eq, Matrix.transpose_apply] at this ⊢
      rw [← this]
      simp
    rw [e2]
    exact h.transpose


omit [NumberField K] in
theorem hform_eq_dot {n : ℕ} (H : Matrix (Fin n) (Fin n) K) (x y : Fin n → K) :
    Formalism.DivisionValues.hform H x y = star x ⬝ᵥ H.mulVec y := by
  unfold Formalism.DivisionValues.hform
  rw [Matrix.toLinearMapₛₗ₂'_apply]
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, Pi.star_apply, starRingEnd_apply, RingHom.id_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring


omit [NumberField K] in
theorem hform_sa {n : ℕ} {H A : Matrix (Fin n) (Fin n) K} (h : Aᴴ * H = H * A) (x y : Fin n → K) :
    Formalism.DivisionValues.hform H (A.mulVec x) y = Formalism.DivisionValues.hform H x (A.mulVec y) := by
  rw [hform_eq_dot, hform_eq_dot, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, h]


omit [NumberField K] [StarRing K] [Fintype G] in
theorem zero_laws [NumberField K] [StarRing K] (σ : K →+* ℂ) {e : MonoidAlgebra K G}
    (hc : e ∈ Subalgebra.center K (MonoidAlgebra K G)) (hi : IsIdempotentElem e) : (Mat1.zero K G).Laws σ e := by
  refine
    { pos := ?_
      lat := ?_
      add := fun _ _ => Subsingleton.elim (α := Matrix (Fin 0) (Fin 0) K) _ _
      smul := fun _ _ => Subsingleton.elim (α := Matrix (Fin 0) (Fin 0) K) _ _
      one := Subsingleton.elim (α := Matrix (Fin 0) (Fin 0) K) _ _
      mul := fun _ _ _ _ => Subsingleton.elim (α := Matrix (Fin 0) (Fin 0) K) _ _
      E_eq := rfl
      cen := hc
      idem := hi
      sa := ?_ }
  · show ((0 : Matrix (Fin 0) (Fin 0) K).map σ).PosDef
    rw [Subsingleton.elim ((0 : Matrix (Fin 0) (Fin 0) K).map σ) 1]
    exact Matrix.PosDef.one
  · change Submodule.IsFullLattice K (⊤ : Submodule (𝓞 K) (Fin 0 → K))
    refine { toIsLattice := Submodule.IsLattice.of_fg K ?_, span_eq_top := Subsingleton.elim _ _ }
    rw [Subsingleton.elim (⊤ : Submodule (𝓞 K) (Fin 0 → K)) ⊥]
    exact Submodule.fg_bot
  · intro x y
    rw [hform_eq_dot, hform_eq_dot]
    rfl

def lvlMat (S : CSD K) (r : Representation K G S.Forms) (P : Subgroup G) (ψ : P →* Kˣ) (e : MonoidAlgebra K G) : Mat1 K G :=
  ⟨S.lvlDim r P ψ, S.lvlH r P ψ, S.lvlOp r P ψ e, S.lvlNab r P ψ, fun a => S.lvlOp r P ψ a⟩

theorem lvlMat_laws {σ : K →+* ℂ} (hσ : ∀ a, σ (star a) = starRingEnd ℂ (σ a)) (S : CSD K) {s : ℕ} (hS : S.Good s)
    (hpos : ∀ v : InfinitePlace K, (S.H.map v.embedding).PosDef) (r : Representation K G S.Forms) (hr : S.ActGood r)
    (hrat : S.ActRat r) (P : Subgroup G) (ψ : P →* Kˣ) (X : Finset (G → K)) (hX : ∀ χ ∈ X, IsAbsIrrChar χ) :
    (lvlMat S r P ψ (idemOf X)).Laws σ (idemOf X) := by
  have h0 := isConjAt_mk hσ
  have hP := (level_idempotent_spec K _ h0 G P ψ).1
  have hI := idempotent_spec K _ h0 G X hX
  have hinj : Function.Injective (S.lvlE r P ψ).mulVec := (image_idempotent_spec K _ _).1
  have hE : ∀ i j, S.lvlE r P ψ i j ∈ Formalism.DivisionValues.cmMax K :=
    image_idempotent_rational K S.dim (S.gaMat r (lvlIdem P ψ)) (gaMat_rat S r hrat _ hP.rat)
  have hproj := (orthogonal_projection_spec K _ h0 S (hpos _) G r hr _ hP.idem hP.selfAdj).1.1
  have hop := level_operator_spec K _ h0 S (hpos _) G r hr P ψ
  refine ⟨posDef_of_mk (cut_posDef S.H (S.lvlE r P ψ) hinj hE (Nat.card P) Nat.card_pos _ (hpos _)),
    (Formalism.DivisionValues.exponent_index_lattice.cut_isFullLattice (S.lvlE r P ψ) hinj _
      (Formalism.DivisionValues.ValuationLatticeField.valLatF_isFullLattice S.I S.I_injective S.Nab hS.nab_isFullLattice)),
    fun a b => ?_, fun c a => ?_, ?_,
    fun a _ b hb => (hop b (Subalgebra.mem_center_iff.1 hb _).symm).2 a, rfl, Subalgebra.mem_center_iff.2 hI.2, hI.1.idem,
    hform_sa ?_⟩
  · show S.lvlOp r P ψ (a + b) = S.lvlOp r P ψ a + S.lvlOp r P ψ b
    unfold CSD.lvlOp
    rw [CSD.gaMat_eq_lift, CSD.gaMat_eq_lift, CSD.gaMat_eq_lift, map_add (f := _), Matrix.mul_add, Matrix.add_mul]
  · show S.lvlOp r P ψ (c • a) = c • S.lvlOp r P ψ a
    unfold CSD.lvlOp
    rw [CSD.gaMat_eq_lift, CSD.gaMat_eq_lift, map_smul, Matrix.mul_smul, Matrix.smul_mul]
  · show S.lvlOp r P ψ 1 = 1
    unfold CSD.lvlOp
    rw [(group_action_matrix_hom K S G r).1, Matrix.mul_one]
    exact hproj
  · have h1 := (hop (idemOf X) (hI.2 _).symm).1
    have h2 := group_action_matrix_adjoint K S G r hr (idemOf X)
    rw [hI.1.selfAdj] at h2
    show (S.lvlOp r P ψ (idemOf X))ᴴ * ((Nat.card P : K)⁻¹ • ((S.lvlE r P ψ)ᴴ * S.H * S.lvlE r P ψ)) =
      ((Nat.card P : K)⁻¹ • ((S.lvlE r P ψ)ᴴ * S.H * S.lvlE r P ψ)) * S.lvlOp r P ψ (idemOf X)
    rw [Matrix.mul_smul, Matrix.smul_mul, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.conjTranspose_mul, h1,
      Matrix.conjTranspose_mul, Matrix.mul_assoc (S.lvlE r P ψ)ᴴ, h2, Matrix.mul_assoc _ (S.lvlE r P ψ), h1]
    simp only [Matrix.mul_assoc]

end Gen

section Col

variable {X : Formalism.L2.Col.Fields} {Pr : Formalism.L2.Col.Primes X} {R : Ranks} (W : Formalism.L2.Col.Wts X Pr.Word R) (Ch : Formalism.L2.Col.Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (hX : X.Ok) (v0 : InfinitePlace X.K)
  (TU : Finset (Tup X.F X.E X.K S)) (Xg : Finset (Formalism.L2.Col.G0 X.E Pr.vGs R.r → X.K)) (S0 : Set (HeightOneSpectrum (𝓞 X.E)))
  (xiVal : Tup X.F X.E X.K S → HeightOneSpectrum (𝓞 X.E) → X.Kˣ) {σ : X.K →+* ℂ} (hσ : ∀ a, σ (star a) = starRingEnd ℂ (σ a))
  (hirr : ∀ χ ∈ Xg, IsAbsIrrChar χ) (P : Subgroup (Formalism.L2.Col.G0 X.E Pr.vGs R.r)) (ψ : P →* X.Kˣ)

include hσ hirr

theorem rows_laws (τ : TupF TU) :
    (lvlMat ((colIn W Ch sel hX v0 TU Xg S0 xiVal).MtildeCSD τ) ((colIn W Ch sel hX v0 TU Xg S0 xiVal).leftGroupActionRight τ) P ψ
      (idemOf Xg)).Laws σ (idemOf Xg) :=
  lvlMat_laws hσ _ (Formalism.L2.Col.MtildeKCSD_good W Ch sel τ.1 hX _) (fun v => (Formalism.L2.Col.mtildeK_rat W Ch sel τ.1 hX).posH _ v) _
    (Formalism.L2.Col.unipotentActionForms_good W Ch sel τ.1 hX _) (Formalism.L2.Col.unipotentActionForms_rational W Ch sel τ.1 hX _) P ψ Xg hirr

theorem lifts_laws (j : Fin R.m) (τ : TupF TU) :
    (lvlMat ((colIn W Ch sel hX v0 TU Xg S0 xiVal).MtCSD j τ) ((colIn W Ch sel hX v0 TU Xg S0 xiVal).leftGroupActionLift j τ) P ψ
      (idemOf Xg)).Laws σ (idemOf Xg) :=
  lvlMat_laws hσ _ (Formalism.L2.Col.MtKCSD_good W Ch sel τ.1 hX (j.1 + 1) _)
    (fun v => (Formalism.L2.Col.mtK_rat W Ch sel τ.1 hX (j.1 + 1)).posH _ v) _
    (Formalism.L2.Col.unipotentActionClassSum_good W Ch sel τ.1 hX (j.1 + 1) _) (Formalism.L2.Col.unipotentActionClassSum_rational W Ch sel τ.1 hX (j.1 + 1) _) P ψ Xg hirr

end Col

section Fam

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} (A : FamIn D.what₂.LL G Pl0 T D.R.m)
  (P : Subgroup G) (ψ : P →* D.what₂.LLˣ)

theorem rMat_eq (t : T) : rMat A P ψ t = lvlMat (A.MtildeCSD t) (A.leftGroupActionRight t) P ψ (idemOf A.X) := rfl

theorem lMat_eq (i : Fin D.R.m) (t : T) : lMat A P ψ i t = lvlMat (A.MtCSD i t) (A.leftGroupActionLift i t) P ψ⁻¹ (idemOf A.X) := rfl

end Fam

theorem mats_laws : ∀ (X : Stages) (px : PreX X.B.toPre) (I : ColIn X.B px) (hX : X.B.fields.Ok) (Xg : Finset (Gc X.B px → X.B.LL)) (tr : TrI X.B px), I.Ok → (∀ χ ∈ Xg, IsAbsIrrChar χ) → (∀ b a, (mAU X I hX Xg tr b a).Laws X.toD7.what₂.embLL (idemOf Xg)) ∧ ∀ a j, (mLU X I hX Xg tr a j).Laws X.toD7.what₂.embLL (idemOf Xg) := by
  intro X px I hX Xg tr _ hirr
  refine ⟨fun b a => ?_, fun a j => ?_⟩
  · unfold mAU
    rw [rMat_eq]
    exact rows_laws (X := X.B.fields) (Pr := X.B.primes px) X.B.wts I.Ch I.sel hX (InfinitePlace.mk X.B.embLL) (tuOf I Set.univ) Xg ∅
      (xiValOf I) (σ := X.B.embLL) X.B.starLL_cx hirr _ _ (tAll I a)
  · unfold mLU
    split_ifs with h
    · rw [lMat_eq]
      exact lifts_laws (X := X.B.fields) (Pr := X.B.primes px) X.B.wts I.Ch I.sel hX (InfinitePlace.mk X.B.embLL) (tuOf I Set.univ) Xg ∅
        (xiValOf I) (σ := X.B.embLL) X.B.starLL_cx hirr _ _ _ (tAll I a)
    · have hI := idempotent_central X.B.LL (Gc X.B px) Xg hirr
      exact zero_laws _ (Subalgebra.mem_center_iff.2 hI.2) hI.1

end GlobalTheory.Mem.R3.Rw.Mats

end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

noncomputable section

namespace GlobalTheory.Mem.R3.Rw

theorem frame_eq_of_map_eq {D : D7} {V : HSp D} {n : ℕ} (P Q : principalLevelFrame.RowPsi V n) (h : P.ψ = Q.ψ) : P = Q := by
  cases P; cases Q; cases h; rfl



theorem lfT_of_same : ∀ (B : Base) (C : Cols B) (a b : Late B C) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (Ks : Type) [Field Ks] [NumberField Ks] [iK : Algebra Ks a.D.what₂.LL] (A : FamIn a.D.what₂.LL G Pl0 T a.D.R.m) (R : RealDat a.D A Ks) (F : Face a.D A) (y : Hd R) (y' : HdB b R), Same b y y' → ∀ (Φ : Type) (rep : Φ → _) (Mt : C.Tup → ℕ → Hs) (l : LfD B.O (B.embLL.comp B.OtoLL) C.Tup Φ Mt) jL (t : LfT y F rep (Mt := Mt) jL l) jL', HEq jL' jL → ∃ t' : @LfT b.D G _ _ Pl0 T (famM b A) Ks _ _ (alg b iK) (real b R) y' (face b F) Φ ((by with_unfolding_all exact (rep :))) Mt jL' l, letI := alg b iK; HEq t'.eW t.eW ∧ HEq t'.jMt t.jMt := by
  intro B C a b G _ _ Pl0 T Ks _ _ iK A R F y y' hs Φ rep Mt l jL t jL' hj
  let yb := y'
  obtain ⟨tup', tupT', _, _, _, _, _, _, PW', _, _, _, _, _⟩ := y'
  obtain ⟨h1, h2, _, h4⟩ := hs
  obtain rfl : tup' = (by with_unfolding_all exact (y.tup :)) := eq_of_heq h1
  obtain rfl : tupT' = (by with_unfolding_all exact (y.tupT :)) := eq_of_heq h2
  have e4 : (fun i => (PW' i).ψ) = (by with_unfolding_all exact ((fun i => (y.PW i).ψ) :)) := eq_of_heq h4
  obtain rfl : PW' = fun i => rowPsi b (y.PW i) :=
    funext fun i => frame_eq_of_map_eq _ _ ((by with_unfolding_all exact ((congrFun e4 i) :)))
  obtain rfl : jL' = (by with_unfolding_all exact (jL :)) := eq_of_heq hj
  letI := alg b iK
  have prt_eq (i : Fin a.D.R.m) (π : Formalism.L2.NG.FinTyp a.D.host.E a.D.R.r) :
      y.prtW F i π = yb.prtW (face b F) i π := by
    unfold Hd.prtW
    rewrite [isotL_eq a b]
    dsimp only [isotLB, rowPsi, ds]
    with_unfolding_all rfl
  have wc_eq := lift_Wc b F y.tupT y.hm y.hTop y.hinj
  have mult_eq := lift_MultW b F y.tupT y.hm y.hTop y.hinj
  refine ⟨{
    eW := (by with_unfolding_all exact (t.eW :))
    eW_range := fun i => by
      with_unfolding_all exact ((t.eW_range i).trans
        (congrArg (fun W => (W i (sg0 a.D A) (R.levL F false (sg0 a.D A))).comap
          (R.HW i (sg0 a.D A)).e) (wat_eq b R)) :)
    eW_norm := (by with_unfolding_all exact (t.eW_norm :))
    eW_lat := (by with_unfolding_all exact (t.eW_lat :))
    jMj := (by with_unfolding_all exact (t.jMj :))
    jMj_read := (by with_unfolding_all exact (t.jMj_read :))
    jMj_inj := (by with_unfolding_all exact (t.jMj_inj :))
    jMj_range := fun i => (by with_unfolding_all exact ((t.jMj_range i).trans (congrFun wc_eq i) :))
    jMj_ip := (by with_unfolding_all exact (t.jMj_ip :))
    jMt := (by with_unfolding_all exact (t.jMt :))
    jMt_inj := (by with_unfolding_all exact (t.jMt_inj :))
    jMt_range := (by with_unfolding_all exact (t.jMt_range :))
    jMt_ip := (by with_unfolding_all exact (t.jMt_ip :))
    theta := fun μ hμ i x h w hw1 he hw2 => by
      let w₀ : (y.L F).AmbW i := by with_unfolding_all exact (w :)
      have hw1' : w₀ ∈ (y.L F).MultW i := by
        rewrite [congrFun mult_eq i]
        with_unfolding_all exact (hw1 :)
      have hw2' : (y.L F).eW i ∘ₗ w₀ ∈ (y.L F).Wc i := by
        rewrite [congrFun wc_eq i]
        with_unfolding_all exact (hw2 :)
      with_unfolding_all exact (t.theta μ hμ i x h w₀ hw1' he hw2' :)
    junk := (by with_unfolding_all exact (t.junk :))
    out := (by with_unfolding_all exact (t.out :))
    isot := fun i π v => by
      with_unfolding_all exact ((t.isot i π v).trans
        (Iff.of_eq (congrArg (fun p => t.jMj i v ∈ p) (prt_eq i (rep π)))) :)
    disj := fun i π π' hne => by
      rewrite [← prt_eq i (rep π), ← prt_eq i (rep π')]
      with_unfolding_all exact (t.disj i π π' hne :)
    read := (by with_unfolding_all exact (t.read :)) }, (by with_unfolding_all exact ((HEq.refl t.eW) :)), (by with_unfolding_all exact ((HEq.refl t.jMt) :))⟩

end GlobalTheory.Mem.R3.Rw
end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.deepElement_conj_rational_at_badPrime : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (a : I.ι) (i : ℕ) (hi : i ≤ B.R.m) (kk : GL (Fin ((I.rec7 l Z).R.N i)) (TensorProduct (I.rec7 l Z).host.F (I.rec7 l Z).host.E (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F))) (fb : SBof I a → GL (Fin ((I.rec7 l Z).R.N i)) (I.rec7 l Z).host.E), FrNear I l Z a kk fb → ∀ (P : SBof I a) (v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F)), Formalism.L2.Col.IsOver v (GlobalTheory.TwU.seamP (sm I l Z) P.1) → ∀ κ ∈ UPts (sigD (I.rec7 l Z)) (gramN (I.rec7 l Z) i hi) (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F), ∀ g ∈ Formalism.L2.Col.GLint B.fields.E (B.R.N i) P.1, GlobalTheory.TwU.InFrame (i := i) (sm I l Z) fb (I.cst a).D P κ g → ∀ x ∈ UPts (sigD (I.rec7 l Z)) (gramN (I.rec7 l Z) i hi) (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F), bc (prV (E := (I.rec7 l Z).host.E) v) x = bc (prV (E := (I.rec7 l Z).host.E) v) κ → ∀ N : ℕ, ∃ z ∈ UPts (sigD (I.rec7 l Z)) (gramN (I.rec7 l Z) i hi) (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F), (∀ v', v' ≠ v → bc (prV (E := (I.rec7 l Z).host.E) v') z = 1) ∧ GlobalTheory.TwU.CongAt (GlobalTheory.TwU.seamP (sm I l Z) P.1) N z ∧ ∃ g' ∈ Formalism.L2.Col.GLint B.fields.E (B.R.N i) P.1, CongE P.1 ((I.cst a).D P) g g' ∧ ∀ r s, adAt (I.rec7 l Z).host.F (GlobalTheory.TwU.seamP (sm I l Z) P.1) ((kk⁻¹ * (x * z) * kk).1 r s) = algebraMap (I.rec7 l Z).host.E ((GlobalTheory.TwU.seamP (sm I l Z) P.1).adicCompletion (I.rec7 l Z).host.E) ((GlobalTheory.TwU.seamGL (sm I l Z) g').1 r s) := by
  first | exact @GlobalTheory.Mem.Col2.AdT.DeepElt.main | exact GlobalTheory.Mem.Col2.AdT.DeepElt.main | (intros; apply GlobalTheory.Mem.Col2.AdT.DeepElt.main <;> assumption)
end
