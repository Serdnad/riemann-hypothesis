module

public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsQuasicoherentOfForallExistsAffine
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsLocalizedModuleResBasicOpenOfQcqs
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle005
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLineBundleGeneratorExtendingDensePart
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.NonemptyIsLimitBaseChange
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.GenericExistsUniqueOActOfIsGrpPullback
public import Formalism.LocalRingCardinality.Bundle005
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import Mathlib.AlgebraicGeometry.QuasiAffine
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
import Mathlib.RingTheory.Coalgebra.CoassocSimps
import Mathlib.RingTheory.PiTensorProduct
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle001
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle007
import Formalism.LocalRingCardinality.DataTheta
public import Formalism.SharpRestriction.Divisibility.InnerProductFormulaField
import Formalism.SharpRestriction.Divisibility.SchurIrreducible

@[expose] public section

section

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CechPic

namespace GlobalTheory.CechPic.Glue

def extUnit {X W : Scheme.{0}} (g : W ⟶ X) [IsOpenImmersion g] (V : W.Opens) : Γ(W, V)ˣ →* Γ(X, g ''ᵁ V)ˣ :=
  Units.map (g.appIso V).inv.hom.toMonoidHom

theorem gm_extUnit {X W T : Scheme.{0}} (g : W ⟶ X) [IsOpenImmersion g] (V : W.Opens) (a : Γ(W, V)ˣ)
    (r : T ⟶ W) (t : T) (ht : r t ∈ V) : gm (r ≫ g) t (g ''ᵁ V) (extUnit g V a) = gm r t V a := by
  have hm : r t ∈ g ⁻¹ᵁ (g ''ᵁ V) := ⟨r t, ht, rfl⟩
  have e : pullU g (g ''ᵁ V) (extUnit g V a) = res (g.preimage_image_eq V).le a :=
    Units.ext (congrArg (fun q => q.hom a.val) (g.appIso_inv_app V))
  rw [← gm_pull r g t _ hm, e, gm_res r t _ hm]

theorem image_inf_le {X W : Scheme.{0}} (g : W ⟶ X) [IsOpenImmersion g] (A B : W.Opens) :
    g ''ᵁ A ⊓ g ''ᵁ B ≤ g ''ᵁ (A ⊓ B) := by
  rintro _ ⟨⟨a, ha, rfl⟩, hb⟩
  exact ⟨a, ⟨ha, (g.apply_mem_image_iff).1 hb⟩, rfl⟩

variable {Y : Scheme.{0}} {κ : Type} {Z : κ → Scheme.{0}} (f : ∀ i, Z i ⟶ Y) [∀ i, IsOpenImmersion (f i)]
  (L : ∀ i, LB (Z i))

def gT (i : κ) (k k' : (L i).ι) : Γ(Y, (f i) ''ᵁ (L i).U k ⊓ (f i) ''ᵁ (L i).U k')ˣ :=
  res (image_inf_le (f i) _ _) (extUnit (f i) _ ((L i).g k k'))


open Classical in
def gS : ∀ p q : (Σ i, (L i).ι),
    Γ(Y, (f p.1) ''ᵁ (L p.1).U p.2 ⊓ (f q.1) ''ᵁ (L q.1).U q.2)ˣ
  | ⟨i, k⟩, ⟨i', k'⟩ => if h : i = i' then by subst h; exact gT f L i k k' else 1

def glueLB : LB Y where
  ι := Σ i, (L i).ι
  U p := (f p.1) ''ᵁ (L p.1).U p.2
  g := gS f L

theorem glueLB_g (i : κ) (k k' : (L i).ι) : (glueLB f L).g ⟨i, k⟩ ⟨i, k'⟩ = gT f L i k k' := by
  show gS f L ⟨i, k⟩ ⟨i, k'⟩ = _
  simp [gS]

theorem gm_glueLB {T : Scheme.{0}} (i : κ) (r : T ⟶ Z i) (t : T) (k k' : (L i).ι) (hk : r t ∈ (L i).U k)
    (hk' : r t ∈ (L i).U k') :
    gm (r ≫ f i) t ((glueLB f L).U ⟨i, k⟩ ⊓ (glueLB f L).U ⟨i, k'⟩) ((glueLB f L).g ⟨i, k⟩ ⟨i, k'⟩) =
      gm r t ((L i).U k ⊓ (L i).U k') ((L i).g k k') := by
  rw [glueLB_g]
  have hm : (r ≫ f i) t ∈ (f i) ''ᵁ (L i).U k ⊓ (f i) ''ᵁ (L i).U k' :=
    ⟨(f i).apply_mem_image_iff.2 hk, (f i).apply_mem_image_iff.2 hk'⟩
  exact (gm_res _ t _ hm _).trans (gm_extUnit (f i) _ _ r t ⟨hk, hk'⟩)

theorem mem_image {X W : Scheme.{0}} (g : W ⟶ X) [IsOpenImmersion g] {A : W.Opens} {y : X} (h : y ∈ g ''ᵁ A) :
    ∃ z ∈ A, g z = y := h

theorem same_of_mem {i i' : κ} (hd : Pairwise fun i i' => Disjoint (f i).opensRange (f i').opensRange) {y : Y}
    (h : y ∈ (f i).opensRange) (h' : y ∈ (f i').opensRange) : i = i' := by
  by_contra hne
  exact (hd hne).le_bot ⟨h, h'⟩

variable {L} in
theorem isLB_glueLB (hL : ∀ i, (L i).IsLB) (hcov : ⨆ i, (f i).opensRange = ⊤)
    (hd : Pairwise fun i i' => Disjoint (f i).opensRange (f i').opensRange) : (glueLB f L).IsLB := {
  cover := by
    refine top_le_iff.1 fun y _ => ?_
    have hy : y ∈ ⨆ i, (f i).opensRange := by rw [hcov]; trivial
    obtain ⟨i, z, rfl⟩ := TopologicalSpace.Opens.mem_iSup.1 hy
    obtain ⟨k, hk⟩ := exists_chart (hL i) z
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨i, k⟩, (f i).apply_mem_image_iff.2 hk⟩
  g_self := by
    rintro ⟨i, k⟩
    refine unit_ext fun y hy => ?_
    obtain ⟨z, hz, rfl⟩ := mem_image (f i) hy
    refine gm_inj (f i) z hy hy ?_
    have e := gm_glueLB f L i (𝟙 _) z k k hz hz
    rw [Category.id_comp] at e
    rw [map_one, gm_res _ z _ hy, e, gm_self (hL i) _ z hz]
  cocycle := by
    rintro ⟨i, k⟩ ⟨i', k'⟩ ⟨i'', k''⟩
    refine unit_ext fun y hy => ?_
    have h1 : y ∈ (f i).opensRange := (f i).image_le_opensRange _ hy.1.1
    have h2 : y ∈ (f i').opensRange := (f i').image_le_opensRange _ hy.1.2
    have h3 : y ∈ (f i'').opensRange := (f i'').image_le_opensRange _ hy.2
    obtain rfl := same_of_mem f hd h1 h2
    obtain rfl := same_of_mem f hd h1 h3
    obtain ⟨z, hz, rfl⟩ := mem_image (f i) hy.1.1
    have hz' : z ∈ (L i).U k' := (f i).apply_mem_image_iff.1 hy.1.2
    have hz'' : z ∈ (L i).U k'' := (f i).apply_mem_image_iff.1 hy.2
    refine gm_inj (f i) z hy hy ?_
    have e1 := gm_glueLB f L i (𝟙 _) z k k' hz hz'
    have e2 := gm_glueLB f L i (𝟙 _) z k' k'' hz' hz''
    have e3 := gm_glueLB f L i (𝟙 _) z k k'' hz hz''
    rw [Category.id_comp] at e1 e2 e3
    rw [map_mul, gm_res _ z _ hy, gm_res _ z _ hy, gm_res _ z _ hy, e1, e2, e3,
      gm_cocycle (hL i) _ z hz hz' hz''] }

theorem exists_pic_glue : ∀ {Y : Scheme.{0}} {κ : Type} [Finite κ] {Z : κ → Scheme.{0}} (f : ∀ i, Z i ⟶ Y)
    [∀ i, IsOpenImmersion (f i)], (⨆ i, (f i).opensRange = ⊤) →
    (Pairwise fun i i' => Disjoint (f i).opensRange (f i').opensRange) →
    ∀ c : ∀ i, Pic (Z i), ∃ d : Pic Y, ∀ i, GlobalTheory.CechPic.pull (f i) d = c i := by
  intro Y κ _ Z f _ hcov hd c
  choose L hL hc using fun i => cls_surj (c i)
  have hG := isLB_glueLB f hL hcov hd
  refine ⟨cls (glueLB f L) hG, fun i => ?_⟩
  rw [← cls_pull hG (f i) (pull_isLB hG (f i)), ← hc i]
  refine Eq.symm ((cls_eq_iff (hL i) (pull_isLB hG (f i))).2 (iso_of_chart (pull_isLB hG (f i)) ?_))
  exact
    { idx := fun k _ => ⟨i, k⟩
      le := fun k z hz => mem_pull.2 ((f i).apply_mem_image_iff.2 hz)
      g := fun z k k' hk hk' => Eq.symm ((gm_pull_g (glueLB f L) (f i) (𝟙 _) z (fun _ => ⟨i, k⟩) (fun _ => ⟨i, k'⟩)
        (mem_pull.2 ((f i).apply_mem_image_iff.2 hk)) (mem_pull.2 ((f i).apply_mem_image_iff.2 hk'))).trans
        (gm_glueLB f L i (𝟙 _) z k k' hk hk')) }

end GlobalTheory.CechPic.Glue
end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory

noncomputable section

namespace GlobalTheory.SecTensor

open TensorProduct

theorem isLocalizedModule_mulTensor {R M N B : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] [CommRing B] [Algebra R B] (r : R) [IsLocalization.Away r B]
    (c : M →ₗ[R] B) (d : N →ₗ[R] B) [IsLocalizedModule.Away r c] [IsLocalizedModule.Away r d] :
    IsLocalizedModule.Away r (TensorProduct.lift ((LinearMap.mul R B).compl₁₂ c d)) := by
  have hc : IsBaseChange B c := (isLocalizedModule_iff_isBaseChange (.powers r) B c).1 inferInstance
  have hd : IsBaseChange B d := (isLocalizedModule_iff_isBaseChange (.powers r) B d).1 inferInstance
  show IsLocalizedModule (.powers r) _
  rw [isLocalizedModule_iff_isBaseChange (.powers r) B]
  have h1 := isBaseChange_tensorProduct_map (R := R) (P := N) B hc
  have h2 := h1.comp (IsBaseChange.ofEquiv hd.equiv)
  have heq : TensorProduct.lift ((LinearMap.mul R B).compl₁₂ c d) =
      (hd.equiv.toLinearMap.restrictScalars R) ∘ₗ
        (AlgebraTensorModule.map c (LinearMap.id (R := R) (M := N))).restrictScalars R := by
    ext m n
    simp [IsBaseChange.equiv_tmul]
  rw [heq]
  exact h2

theorem bijective_of_mulTensor {R M N P : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] [AddCommGroup P] [Module R P] (μ : M ⊗[R] N →ₗ[R] P)
    (s : Set R) (hs : Ideal.span s = ⊤) (B : s → Type*) [∀ r, CommRing (B r)]
    [∀ r, Algebra R (B r)] [∀ r : s, IsLocalization.Away r.1 (B r)]
    (c : ∀ r, M →ₗ[R] B r) (d : ∀ r, N →ₗ[R] B r) (e : ∀ r, P →ₗ[R] B r)
    [∀ r : s, IsLocalizedModule.Away r.1 (c r)] [∀ r : s, IsLocalizedModule.Away r.1 (d r)]
    [∀ r : s, IsLocalizedModule.Away r.1 (e r)]
    (h : ∀ r m n, e r (μ (m ⊗ₜ n)) = c r m * d r n) : Function.Bijective μ := by
  have (r : s) := isLocalizedModule_mulTensor r.1 (c r) (d r)
  refine bijective_of_isLocalized_span s hs (fun r => B r)
    (fun r => TensorProduct.lift ((LinearMap.mul R (B r)).compl₁₂ (c r) (d r))) (fun r => B r) e μ
    fun r => ?_
  have : IsLocalizedModule.map (.powers r.1)
      (TensorProduct.lift ((LinearMap.mul R (B r)).compl₁₂ (c r) (d r))) (e r) μ = LinearMap.id := by
    apply IsLocalizedModule.linearMap_ext (.powers r.1)
      (TensorProduct.lift ((LinearMap.mul R (B r)).compl₁₂ (c r) (d r))) (e r)
    rw [IsLocalizedModule.map_comp]
    ext m n
    simp [h]
  rw [this]
  exact Function.bijective_id

end GlobalTheory.SecTensor

namespace GlobalTheory.SecTensor

open TensorProduct GlobalTheory.LB

variable {T : Scheme.{0}}

def mulFun (A B : LB T) (s : LB.Sec A) (t : LB.Sec B) (p : A.ι × B.ι) :
    Γ(T, A.U p.1 ⊓ B.U p.2) :=
  resG T (inf_le_left : A.U p.1 ⊓ B.U p.2 ≤ A.U p.1) (s.f p.1) *
    resG T (inf_le_right : A.U p.1 ⊓ B.U p.2 ≤ B.U p.2) (t.f p.2)

def mulSec (A B : LB T) (s : LB.Sec A) (t : LB.Sec B) : LB.Sec (CechPic.tens A B) where
  f := mulFun A B s t
  compat := fun (p q : A.ι × B.ι) => by
    unfold CechPic.tens
    change resG T _ (_ * _) = _ * resG T _ (_ * _)
    simp only [map_mul, resG_resG]
    rw [sec_rel s p.1 q.1 (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left)
        (le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left)),
      sec_rel t p.2 q.2 (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right)
        (le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right))]
    simp only [Units.val_mul, val_res, resG_resG]
    ring

def mulBil (A B : LB T) :
    LB.Sec A →ₗ[Γ(T, ⊤)] LB.Sec B →ₗ[Γ(T, ⊤)] LB.Sec (CechPic.tens A B) :=
  LinearMap.mk₂ Γ(T, ⊤) (mulSec A B)
    (fun s s' t => f_injective (show mulFun A B (s + s') t = mulFun A B s t + mulFun A B s' t from
      funext fun p => by simp only [mulFun, add_f, map_add (f := _), add_mul, Pi.add_apply]))
    (fun a s t => f_injective (show mulFun A B (a • s) t =
      fun (p : A.ι × B.ι) => resG T (le_top : A.U p.1 ⊓ B.U p.2 ≤ ⊤) a * mulFun A B s t p
      from funext fun p => by simp only [mulFun, smul_f, map_mul, resG_resG]; ring))
    (fun s t t' => f_injective (show mulFun A B s (t + t') = mulFun A B s t + mulFun A B s t' from
      funext fun p => by simp only [mulFun, add_f, map_add (f := _), mul_add, Pi.add_apply]))
    (fun a s t => f_injective (show mulFun A B s (a • t) =
      fun (p : A.ι × B.ι) => resG T (le_top : A.U p.1 ⊓ B.U p.2 ≤ ⊤) a * mulFun A B s t p
      from funext fun p => by simp only [mulFun, smul_f, map_mul, resG_resG]; ring))

def chartLoc (L : LB T) (r : Γ(T, ⊤)) (i : L.ι) (h : T.basicOpen r ≤ L.U i) :
    LB.Sec L →ₗ[Γ(T, ⊤)] Γ(T, T.basicOpen r) where
  toFun s := resG T h (s.f i)
  map_add' s t := by simp only [add_f, map_add (f := _)]
  map_smul' a s := by
    simp only [smul_f, map_mul, resG_resG, RingHom.id_apply, Algebra.smul_def]
    rfl

end GlobalTheory.SecTensor

namespace GlobalTheory.SecTensor

open TensorProduct GlobalTheory.LB

variable {T : Scheme.{0}}

def chartEquivTop (L : LB T) (hL : L.IsLB) (r : Γ(T, ⊤)) (i : L.ι) (h : T.basicOpen r ≤ L.U i) :
    AbLaw.SecOn L (T.basicOpen r) ≃ₗ[Γ(T, ⊤)] Γ(T, T.basicOpen r) where
  toFun s := resG T (le_inf le_rfl h) (coord s i)
  invFun a := a • (toMod L).presheaf.map (homOfLE h).op (chartSec hL i)
  map_add' s t := by simp only [coord_add, map_add (f := _)]
  map_smul' a s := by
    rw [AbLaw.SecOn.smul_basicOpen_def, Algebra.smul_def]
    simp only [coord_smul, map_mul, resG_resG, RingHom.id_apply]
    rfl
  left_inv s := Subtype.ext (funext fun j => by
    change coord (_ • _) j = coord s j
    simp only [coord_smul, coord_map, coord_chartSec, resG_resG]
    rw [mul_comm, ← coord_rel s j i le_rfl, resG_self])
  right_inv a := by
    simp only [coord_smul, coord_map, coord_chartSec, resG_resG, resG_self,
      resG_g_self hL, map_one, mul_one]

theorem isLocalizedModule_chartLoc [IsAffine T] (L : LB T) (hL : L.IsLB) (r : Γ(T, ⊤)) (i : L.ι)
    (h : T.basicOpen r ≤ L.U i) : IsLocalizedModule.Away r (chartLoc L r i h) := by
  haveI := AbLaw.SecOn.isLocalizedModule_resBasicOpen hL (isAffineOpen_top T) r
  haveI := IsLocalizedModule.of_linearEquiv (S := .powers r) (f := AbLaw.SecOn.resBasicOpen L r)
    (chartEquivTop L hL r i h)
  let toTop : LB.Sec L →ₗ[Γ(T, ⊤)] AbLaw.SecOn L ⊤ :=
    { toFun := fun s => ofSec s ⊤
      map_add' := fun s t => Subtype.ext (funext fun i => by
        change coord (ofSec (s + t) ⊤) i = coord (ofSec s ⊤ + ofSec t ⊤) i
        simp only [coord_ofSec, coord_add, add_f, map_add (f := _)])
      map_smul' := fun a s => Subtype.ext (funext fun i => by
        change coord (ofSec (a • s) ⊤) i = coord (a • ofSec s ⊤) i
        simp only [coord_ofSec, coord_smul, smul_f, map_mul, resG_resG]) }
  let topEquiv := LinearEquiv.ofBijective toTop (AbLaw.SecOn.ofSec_bijective (M := L) rfl)
  haveI := IsLocalizedModule.of_linearEquiv_right (S := .powers r)
    (f := (chartEquivTop L hL r i h).toLinearMap ∘ₗ AbLaw.SecOn.resBasicOpen L r)
    topEquiv
  have e : chartLoc L r i h = ((chartEquivTop L hL r i h).toLinearMap ∘ₗ
      AbLaw.SecOn.resBasicOpen L r) ∘ₗ topEquiv.toLinearMap := by
    ext s
    change resG T h (s.f i) = resG T (le_inf le_rfl h)
      (coord ((toMod L).presheaf.map (homOfLE (T.basicOpen_le r)).op (ofSec s ⊤)) i)
    rw [map_ofSec, coord_ofSec, resG_resG]
  rw [e]
  infer_instance

end GlobalTheory.SecTensor

namespace GlobalTheory.SecTensor

open TensorProduct GlobalTheory.LB

theorem tensorSecEquiv : ∀ (T : Scheme.{0}) [IsAffine T] (A B : LB T), A.IsLB → B.IsLB →
    Nonempty (TensorProduct Γ(T, ⊤) (LB.Sec A) (LB.Sec B) ≃ₗ[Γ(T, ⊤)]
      LB.Sec (GlobalTheory.CechPic.tens A B)) := by
  intro T _ A B hA hB
  let s : Set Γ(T, ⊤) := {f | ∃ i j, T.basicOpen f ≤ A.U i ⊓ B.U j}
  have hs : Ideal.span s = ⊤ := by
    rw [← (isAffineOpen_top T).self_le_iSup_basicOpen_iff]
    intro x hx
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 (hA.cover.ge (TopologicalSpace.Opens.mem_top x))
    obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 (hB.cover.ge (TopologicalSpace.Opens.mem_top x))
    obtain ⟨f, hf, hxf⟩ := (isAffineOpen_top T).exists_basicOpen_le (V := A.U i ⊓ B.U j) ⟨x, hi, hj⟩ hx
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨f, i, j, hf⟩, hxf⟩
  have (r : s) := (isAffineOpen_top T).isLocalization_basicOpen r.1
  let i (r : s) : A.ι := r.2.choose
  let j (r : s) : B.ι := r.2.choose_spec.choose
  have hij (r : s) : T.basicOpen r.1 ≤ A.U (i r) ⊓ B.U (j r) := r.2.choose_spec.choose_spec
  have (r : s) := isLocalizedModule_chartLoc A hA r.1 (i r) ((hij r).trans inf_le_left)
  have (r : s) := isLocalizedModule_chartLoc B hB r.1 (j r) ((hij r).trans inf_le_right)
  have (r : s) := isLocalizedModule_chartLoc (CechPic.tens A B) (CechPic.isLB_tens hA hB) r.1
    ((i r, j r) : A.ι × B.ι) (hij r)
  refine ⟨LinearEquiv.ofBijective (TensorProduct.lift (mulBil A B))
    (bijective_of_mulTensor _ s hs (fun r => Γ(T, T.basicOpen r.1))
      (fun r => chartLoc A r.1 (i r) ((hij r).trans inf_le_left))
      (fun r => chartLoc B r.1 (j r) ((hij r).trans inf_le_right))
      (fun r => chartLoc (CechPic.tens A B) r.1 ((i r, j r) : A.ι × B.ι) (hij r))
      fun r m n => ?_)⟩
  rw [TensorProduct.lift.tmul]
  change resG T (hij r) (mulFun A B m n (i r, j r)) = _ * _
  simp only [mulFun, map_mul, resG_resG]
  rfl

end GlobalTheory.SecTensor
end
end

section

open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.CechPic

theorem eq_zero_of_pull_densePart_of_pull_section : ∀ {S Y U YU : Scheme.{0}} [IsLocallyNoetherian S]
    [GlobalTheory.IsNormalScheme S] (f : Y ⟶ S) [Smooth f] [GeometricallyConnected f] (j : U ⟶ S)
    [IsOpenImmersion j] (ρ : YU ⟶ Y) (fU : YU ⟶ U), Dense (Set.range j) → IsPullback ρ fU f j →
    ∀ σ : S ⟶ Y, σ ≫ f = 𝟙 S → ∀ δ : GlobalTheory.CechPic.Pic Y, GlobalTheory.CechPic.pull ρ δ = 0 →
      GlobalTheory.CechPic.pull σ δ = 0 → δ = 0 := by
  intro S Y U YU _ _ f _ _ j _ ρ fU hd hpb σ hσ δ hρ hσδ
  obtain ⟨N, hN, rfl⟩ := cls_surj δ
  have hdom : IsDominant j := ⟨hd⟩
  have hgi : GeometricallyIntegral f :=
    GlobalTheory.forall_geometricallyIntegral_of_smooth_of_geometricallyConnected Y S f inferInstance inferInstance
  have hfst : pullback.fst f j = hpb.isoPullback.inv ≫ ρ := (IsPullback.isoPullback_inv_fst hpb).symm
  have h1 : cls (N.pull σ) (pull_isLB hN σ) = 0 := by rw [cls_pull hN]; exact hσδ
  have h2 : cls (N.pull (pullback.fst f j)) (pull_isLB hN _) = 0 := by
    rw [cls_pull hN, hfst, pull_comp, hρ, map_zero]
  obtain ⟨t, ht⟩ := GlobalTheory.GenericExtend.exists_isGen_of_densePart S U j (GlobalTheory.IsNormalScheme.pred S)
    inferInstance inferInstance hdom inferInstance (Over.mk f) σ N hσ (show Smooth f from inferInstance) hgi hN
    ((cls_eq_zero_iff _).1 h1) ((cls_eq_zero_iff _).1 h2)
  exact (cls_eq_zero_iff hN).2 ⟨t, ht⟩

end GlobalTheory.CechPic
end

section

open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

noncomputable section

namespace GlobalTheory.StalkLBIso

set_option backward.isDefEq.respectTransparency false

theorem lbIso_pull_iff {X Y : Scheme.{0}} {A B : LB X} (hA : A.IsLB) (hB : B.IsLB) (f : Y ⟶ X) :
    LBIso (A.pull f) (B.pull f) ↔
      CechPic.pull f (CechPic.cls A hA) = CechPic.pull f (CechPic.cls B hB) := by
  rw [← CechPic.cls_pull hA f (pull_isLB hA f), ← CechPic.cls_pull hB f (pull_isLB hB f)]
  exact (CechPic.cls_eq_iff _ _).symm

theorem exists_lbIso_nhd : ∀ {S X : Scheme.{0}} [IsLocallyNoetherian S] (h : X ⟶ S) [QuasiCompact h]
    [QuasiSeparated h] (x : S) (A B : LB X), A.IsLB → B.IsLB →
    LBIso (A.pull (pullback.fst h (S.fromSpecStalk x))) (B.pull (pullback.fst h (S.fromSpecStalk x))) →
    ∃ W : S.Opens, x ∈ W ∧ LBIso (A.pull (h ⁻¹ᵁ W).ι) (B.pull (h ⁻¹ᵁ W).ι) := by
  intro S X _ h _ _ x A B hA hB hAB

  have hpb : IsPullback (pullback.fst h (S.fromSpecStalk x)) (pullback.snd h (S.fromSpecStalk x)) h
      (S.fromSpecStalk x) := IsPullback.of_hasPullback _ _
  have hc := (GlobalTheory.StalkLimit.nonempty_isLimit hpb).some
  obtain ⟨V₀⟩ : Nonempty (GlobalTheory.StalkLimit.AffNhd x) := IsCofiltered.nonempty
  have : IsAffine V₀.1.toScheme := V₀.2.2
  have : CompactSpace ((GlobalTheory.StalkLimit.diagram x h).obj V₀) :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.snd h V₀.1.ι)
  have : QuasiSeparatedSpace ((GlobalTheory.StalkLimit.diagram x h).obj V₀) :=
    quasiSeparatedSpace_of_quasiSeparated (pullback.snd h V₀.1.ι)

  have h0 : LBIso ((A.pull (pullback.fst h V₀.1.ι)).pull ((GlobalTheory.StalkLimit.cone hpb).π.app V₀))
      ((B.pull (pullback.fst h V₀.1.ι)).pull ((GlobalTheory.StalkLimit.cone hpb).π.app V₀)) := by
    rw [lbIso_pull_iff (pull_isLB hA _) (pull_isLB hB _), CechPic.cls_pull hA, CechPic.cls_pull hB,
      ← CechPic.pull_comp, ← CechPic.pull_comp, GlobalTheory.StalkLimit.cone_π_fst, ← lbIso_pull_iff hA hB]
    exact hAB

  obtain ⟨j, f, hj⟩ := GlobalTheory.exists_lbIso_of_isLimit (GlobalTheory.StalkLimit.diagram x h)
    (fun V => (GlobalTheory.StalkLimit.cone hpb).π.app V) (fun f => (GlobalTheory.StalkLimit.cone hpb).w f) hc
    (A.pull (pullback.fst h V₀.1.ι)) (B.pull (pullback.fst h V₀.1.ι)) (pull_isLB hA _) (pull_isLB hB _) h0
  have hj' : CechPic.pull (pullback.fst h j.1.ι) (CechPic.cls A hA) =
      CechPic.pull (pullback.fst h j.1.ι) (CechPic.cls B hB) := by
    rw [lbIso_pull_iff (pull_isLB hA _) (pull_isLB hB _), CechPic.cls_pull hA, CechPic.cls_pull hB,
      ← CechPic.pull_comp, ← CechPic.pull_comp, GlobalTheory.StalkLimit.diagram_map_fst] at hj
    exact hj

  refine ⟨j.1, j.2.1, ?_⟩
  rw [lbIso_pull_iff hA hB, ← pullbackRestrictIsoRestrict_inv_fst, CechPic.pull_comp, CechPic.pull_comp, hj']

end GlobalTheory.StalkLBIso
end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH MeasureTheory NumberField IsDedekindDomain
open Formalism.MainNotions.SchurIrreducible (IrrGK)
open GlobalTheory.IndefiniteRowSideFullHecke.MatrixMinorProducts (delta wtK wtExt wtH IsLowestType IsKIntw)
open GlobalTheory.IndefiniteRowSideFullHecke.EulerProductLocalFactors (Place eulerProd dPart quadSign SatakeBound)
open scoped TensorProduct

namespace GlobalTheory.BlockSizes

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def rowsP (D : D7) (j : ℕ) (τ : D.what₂.Tau) (i : Fin (D.R.sigW j).1) : ℕ := ⌊DV.aPlusQ D j τ i⌋₊

def rowsM (D : D7) (j : ℕ) (τ : D.what₂.Tau) (i : Fin (D.R.sigW j).2) : ℕ :=
  ⌊DV.aMinusQ D j τ ((D.R.sigW j).2 - 1 - i)⌋₊

variable {D : D7} (X : Formalism.MainNotions.InnerProductFormulaField.Loc D)

def WindowsLe (L : SizeData₂ D) : Prop := L.etaSz ≤ L.sc.b ∧ L.Sc ≤ L.sc.b

end GlobalTheory.BlockSizes

end
end
