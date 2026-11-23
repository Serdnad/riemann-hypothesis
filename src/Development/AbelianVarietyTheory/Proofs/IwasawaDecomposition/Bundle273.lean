module

public import Formalism.LocalToGlobal.IndefiniteReal.GramCEqTranspose
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
import Formalism.LocalToGlobal.Divisibility.RowLatLemmas
import Formalism.LocalToGlobal.IndefiniteReal.LiftCoordinatesInGoodPartFamily
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle014
public import Formalism.LocalToGlobal.IndefiniteReal.PrincipalLevelFrame
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle482
public import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle081
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle001
import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.LocalToGlobal.Columns.CoefficientsModP.WeTransposeWordTransposeWord
import Formalism.LocalToGlobal.Divisibility.CoefMod
import Formalism.LocalToGlobal.HilbertRowConditions.CenterIdempotentAction
import Formalism.LocalToGlobal.IndefiniteForms.IndefSide
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
import Formalism.LocalToGlobal.IndefiniteReal.RecTie
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedCoefficientFieldInComplex
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle003
import Development.AbelianVarietyTheory.PublishedTheorems.AdelicLattices₂.AlgebraMapNormOfBasisOneSqrt

@[expose] public section

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.Mem GlobalTheory.Mem.R3
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory

theorem formsL_exists_baseChange_coordinates : ∀ {L L' Ks : Type} [Field L] [NumberField L] [Field L'] [NumberField L'] [Field Ks] [NumberField Ks] [Algebra Ks L] [Algebra Ks L'] (ι : L →+* L'), (∀ y : Ks, ι (algebraMap Ks L y) = algebraMap Ks L' y) → ∀ (n : ℕ) (W : (L →+* ℂ) → Type) [∀ σ, NormedAddCommGroup (W σ)] [∀ σ, InnerProductSpace ℂ (W σ)] (G : Type) [Group G] (F : Formalism.IndefR.Arith.FormsL L Ks (Fin n → L) W G),
  ∃ F' : Formalism.IndefR.Arith.FormsL L' Ks (Fin n → L') (fun σ' => W (σ'.comp ι)) G,
    (∀ (σ' : L' →+* ℂ) (x : Fin n → L), F'.j σ' (fun k => ι (x k)) = F.j (σ'.comp ι) x) ∧
    (∀ x' : Fin n → L', x' ∈ F'.WK ↔ ∃ x ∈ F.WK, x' = fun k => ι (x k)) ∧
    (∀ g, ((F'.chi g : L'ˣ) : L') = ι ((F.chi g : Lˣ) : L)) ∧
    (∀ g (x : Fin n → L), F'.ρ g (fun k => ι (x k)) = fun k => ι (F.ρ g x k)) ∧
    F'.Pt = F.Pt ∧
    ∀ lp (y' : F'.Pt lp) (y : F.Pt lp), HEq y' y → ∀ (φ' : F'.WK) (φ : F.WK), (φ'.1 = fun k => ι (φ.1 k)) → F'.nrm lp y' φ' = F.nrm lp y φ := by
  intro L L' Ks _ _ _ _ _ _ _ _ ι hι n W _ _ G _ F
  let m : (Fin n → L) →ₗ[Ks] (Fin n → L') :=
    { toFun := fun x k => ι (x k)
      map_add' := fun x y => by funext k; simp
      map_smul' := fun c x => by
        funext k
        simp only [Pi.smul_apply, RingHom.id_apply, Algebra.smul_def, map_mul, hι] }
  have minj : Function.Injective m := by
    intro x y h
    funext k
    exact ι.injective (congrFun h k)
  let e := Submodule.equivMapOfInjective m minj F.WK
  let ρ' : G →* ((Fin n → L') →ₗ[L'] (Fin n → L')) :=
    (Matrix.toLinAlgEquiv' (R := L') (n := Fin n)).toMonoidHom.comp
      ((ι.mapMatrix (m := Fin n)).toMonoidHom.comp
        ((LinearMap.toMatrixAlgEquiv' (R := L) (n := Fin n)).toMonoidHom.comp F.ρ))
  let j' : ∀ σ' : L' →+* ℂ, (Fin n → L') →ₛₗ[σ'] W (σ'.comp ι) := fun σ' =>
    { toFun := fun x' => ∑ k, σ' (x' k) • F.j (σ'.comp ι) (Pi.single k 1)
      map_add' := fun x y => by
        simp only [Pi.add_apply, map_add (f := _), add_smul, Finset.sum_add_distrib]
      map_smul' := fun c x => by
        simp only [Pi.smul_apply, smul_eq_mul, map_mul, mul_smul, Finset.smul_sum] }
  let F' : Formalism.IndefR.Arith.FormsL L' Ks (Fin n → L') (fun σ' => W (σ'.comp ι)) G :=
    { WK := F.WK.map m
      Pt := F.Pt
      nrm := fun lp y φ' => F.nrm lp y (e.symm φ')
      nrm_nonneg := fun lp y f => F.nrm_nonneg lp y _
      nrm_zero := fun lp y => by rw [e.symm.map_zero]; exact F.nrm_zero lp y
      nrm_add := fun lp y f g => by rw [e.symm.map_add]; exact F.nrm_add lp y _ _
      nrm_smul := fun lp y a f => by rw [e.symm.map_smul]; exact F.nrm_smul lp y a _
      towKs := inferInstance
      ρ := ρ'
      chi := (Units.map ι.toMonoidHom).comp F.chi
      j := j' }
  refine ⟨F', ?_, ?_, ?_, ?_, rfl, ?_⟩
  · intro σ' x
    have hx : x = ∑ k, x k • (Pi.single k 1 : Fin n → L) := by
      funext i; simp [Finset.sum_apply, Pi.single_apply]
    show ∑ k, σ' (ι (x k)) • F.j (σ'.comp ι) (Pi.single k 1) = F.j (σ'.comp ι) x
    conv_rhs => rw [hx]

    simp only [map_sum, map_smulₛₗ, RingHom.comp_apply]
  · intro x'
    show x' ∈ F.WK.map m ↔ _
    rw [Submodule.mem_map]
    constructor
    · rintro ⟨x, hx, rfl⟩; exact ⟨x, hx, rfl⟩
    · rintro ⟨x, hx, rfl⟩; exact ⟨x, hx, rfl⟩
  · intro g; rfl
  · intro g x
    show Matrix.toLin' ((LinearMap.toMatrix' (F.ρ g)).map ι) (fun k => ι (x k)) = _
    funext k
    rw [Matrix.toLin'_apply]
    have := RingHom.map_mulVec ι (LinearMap.toMatrix' (F.ρ g)) x k
    rw [LinearMap.toMatrix'_mulVec] at this
    exact this.symm
  · intro lp y' y hy φ' φ hφ
    have hyy : y' = y := eq_of_heq hy
    subst hyy
    show F.nrm lp y' (e.symm φ') = F.nrm lp y' φ
    have : φ' = e φ := Subtype.ext hφ
    rw [this, LinearEquiv.symm_apply_apply]

end GlobalTheory
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

noncomputable section
namespace GlobalTheory.Mem.R3

section Gen

theorem majAt_eq_zero_of_self {K V ι : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
    [Fintype ι] [DecidableEq ι] (b : Module.Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (v : InfinitePlace K) {x : V}
    (h : Formalism.HermitianLatticesTheory.majAt b X v x x = 0) (y : V) : Formalism.HermitianLatticesTheory.majAt b X v x y = 0 := by
  unfold Formalism.HermitianLatticesTheory.majAt at h ⊢
  have hz : ∀ i, Formalism.HermitianLatticesTheory.fcoord b X v x i = 0 := by
    have h1 : ∀ i, star (Formalism.HermitianLatticesTheory.fcoord b X v x i) * Formalism.HermitianLatticesTheory.fcoord b X v x i =
        ((Complex.normSq (Formalism.HermitianLatticesTheory.fcoord b X v x i) : ℝ) : ℂ) := fun i => by
      rw [mul_comm]; exact Complex.mul_conj _
    simp only [h1] at h
    have h2 : ∑ i, Complex.normSq (Formalism.HermitianLatticesTheory.fcoord b X v x i) = 0 := by exact_mod_cast h
    intro i
    have := (Finset.sum_eq_zero_iff_of_nonneg fun j _ => Complex.normSq_nonneg _).1 h2 i (Finset.mem_univ _)
    exact Complex.normSq_eq_zero.1 this
  simp [hz]

theorem partPr_of_bot {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K} (Df : DefSide Bs) (t : Bs.Tup) (p : Bs.Ix)
    (h : Df.Qp t p = ⊥) : partPr Df t p = 0 := by
  unfold partPr
  split_ifs with hc
  · have hz : ∀ z ∈ Df.Qp t p, z = 0 := fun z hz => by
      rw [h] at hz
      exact (Submodule.mem_bot K).1 hz
    ext i j
    rw [LinearMap.toMatrix'_apply, LinearMap.comp_apply, Submodule.subtype_apply, hz _ (Submodule.coe_mem _)]
    rfl
  · rfl

theorem rowXE_congr {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K} (Df : DefSide Bs)
    (Y : Matrix (Fin (Df.dQ Bs.μ0)) (Fin (Df.dQ Bs.μ0)) ℂ) (κ : InfinitePlace K → ℝ) (lam lam' : Bs.J → Bs.Ix → InfinitePlace K → ℝ)
    (h : ∀ p, partPr Df Bs.μ0 p ≠ 0 → ∀ j v, lam j p v = lam' j p v) : rowXE Df Y κ lam = rowXE Df Y κ lam' := by
  have hw : weightMet (partPr Df Bs.μ0) (fun p v => κ v * ∏ j, lam j p v) (Df.XQ Bs.μ0) =
      weightMet (partPr Df Bs.μ0) (fun p v => κ v * ∏ j, lam' j p v) (Df.XQ Bs.μ0) := by
    funext v
    unfold weightMet
    refine Finset.sum_congr rfl fun p _ => ?_
    by_cases hp : partPr Df Bs.μ0 p = 0
    · rw [hp]
      simp [restrMetC]
    · simp only [h p hp]
  unfold rowXE rowFrame weightFrame
  rw [hw]

end Gen

section GenCx2
variable {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K} {A : DefAmb Bs} {fc : DefSub A → DefFace Bs}

theorem cx_XE_scal (Y : CxData A) (cr : Crd A fc) (lam : type_of% Y.lam) (b : Bool)
    (h : ∀ p, partPr (lv (fc Y.zs) b) Bs.μ0 p ≠ 0 → ∀ j v, lam j Bs.μ0 p v = Y.lam j Bs.μ0 p v) :
    ((reScal Y Y.κ lam).data cr b).XE = (Y.data cr b).XE :=
  rowXE_congr _ _ _ _ _ h

theorem cx_galD_scal (Y : CxData A) (cr : Crd A fc) (κ : InfinitePlace K → ℝ) (lam : type_of% Y.lam)
    (hlam : ∀ j p v, v ≠ Bs.v0 → (∃ x, Y.tC cr false j Bs.μ0 (cpt Bs.v0.embedding x) ∈ Y.Wp j p ∧
      Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K _) ((lv (fc Y.zs) false).XT j Bs.μ0) v x x ≠ 0) → lam j Bs.μ0 p v = Y.lam j Bs.μ0 p v)
    (h : Y.GalD cr false) : (reScal Y κ lam).GalD cr false := by
  intro j v hv p x hx y
  have h0 := h j v hv p x hx y
  refine h0.trans ?_
  show _ = ((lam j Bs.μ0 p v : ℝ) : ℂ) * Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K _) ((lv (fc Y.zs) false).XT j Bs.μ0) v x y
  by_cases hp : ∃ x, Y.tC cr false j Bs.μ0 (cpt Bs.v0.embedding x) ∈ Y.Wp j p ∧
      Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K _) ((lv (fc Y.zs) false).XT j Bs.μ0) v x x ≠ 0
  · erw [hlam j p v hv hp] <;> rfl
  · have hxx : Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K _) ((lv (fc Y.zs) false).XT j Bs.μ0) v x x = 0 := by
      by_contra hne
      exact hp ⟨x, hx, hne⟩
    erw [majAt_eq_zero_of_self _ _ v hxx y] <;> simp only [mul_zero]

end GenCx2

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]


open Classical in
def zeroLam (R : RealDat3 D A3 Ks) (F : Face3 D A3) (c : Fin D.R.m → ℝ) : type_of% R.lam3 :=
  fun i t p v => if (v = A3.A.v0 ∧ R.Wp3 i p = ⊥) ∨ (v ≠ A3.A.v0 ∧ ¬ R.PartAt F i p v) then Real.exp (c i) else R.lam3 i t p v

theorem zeroLam_of_ne (R : RealDat3 D A3 Ks) (F : Face3 D A3) (c : Fin D.R.m → ℝ) {i t p v}
    (h1 : R.Wp3 i p ≠ ⊥) (h2 : v ≠ A3.A.v0 → R.PartAt F i p v) : zeroLam R F c i t p v = R.lam3 i t p v := by
  unfold zeroLam
  rw [if_neg]
  rintro (⟨_, h⟩ | ⟨hv, h⟩)
  · exact h1 h
  · exact h (h2 hv)

theorem scalarsZeroPartConvention_fixedPlace (R : RealDat3 D A3 Ks) (F : Face3 D A3) (c : Fin D.R.m → ℝ) {i t p}
    (h1 : R.Wp3 i p ≠ ⊥) : zeroLam R F c i t p A3.A.v0 = R.lam3 i t p A3.A.v0 :=
  zeroLam_of_ne R F c h1 fun h => absurd rfl h

theorem zeroLam_off (R : RealDat3 D A3 Ks) (F : Face3 D A3) (c : Fin D.R.m → ℝ) {i t p v}
    (hv : v ≠ A3.A.v0) (h2 : R.PartAt F i p v) : zeroLam R F c i t p v = R.lam3 i t p v := by
  unfold zeroLam
  rw [if_neg]
  rintro (⟨h, _⟩ | ⟨_, h⟩)
  · exact hv h
  · exact h h2

theorem zeroLam_of_zero (R : RealDat3 D A3 Ks) (F : Face3 D A3) (c : Fin D.R.m → ℝ) {i t p v}
    (h : (v = A3.A.v0 ∧ R.Wp3 i p = ⊥) ∨ (v ≠ A3.A.v0 ∧ ¬ R.PartAt F i p v)) : zeroLam R F c i t p v = Real.exp (c i) := by
  unfold zeroLam
  rw [if_pos h]

theorem zeroLam_pos (R : RealDat3 D A3 Ks) (F : Face3 D A3) (c : Fin D.R.m → ℝ) (h : ∀ i t p v, 0 < R.lam3 i t p v) (i t p v) :
    0 < zeroLam R F c i t p v := by
  unfold zeroLam
  split_ifs
  · exact Real.exp_pos _
  · exact h i t p v



theorem qp_bot (R : RealDat3 D A3 Ks) (F : Face3 D A3) (hC : R.WeakCharacterisation F) (hP : PrimRows3 R F) (hOk : A3.fam3.Ok3 1)
    (hsep : A3.fam3.TypesSep3) {p : A3.fam3.base3.Ix} (hp : R.EEp3 p = ⊥) (b : Bool) :
    (lv (F.fc (R.toCx3 F).zs) b).Qp A3.fam3.base3.μ0 p = ⊥ := by
  have kR := RealDat3.kFormR_of (F := F) hC.base.models
  have hst := (subspaces_stable_in_block (complex_data_conditions_base_level_of_primitive_links hOk hsep hC hP)).1
  have hH := hP.hecke.1.choose_spec
  have key : ∀ ℓ y, y ∈ (A3.fam3.RI A3.fam3.F.μ0).part3 ℓ ((R.toCx3 F).Z A3.fam3.F.μ0) p.1 → y = 0 := by
    intro ℓ y hy
    have h1 := (part_iff_rows3 kR hst hOk hH p ℓ y).1 hy
    have h2 : (R.toCx3 F).Θ A3.fam3.F.μ0 ((R.toCx3 F).jR A3.fam3.F.μ0
        ((A3.fam3.F.R A3.fam3.F.μ0).toF ℓ ((R.toCx3 F).Z A3.fam3.F.μ0) y)) = 0 := by
      have h3 : Tw.out (s := twAt D.what₂.embLL A3.A.v0) (E := R.HE.H) ((R.toCx3 F).Θ A3.fam3.F.μ0 ((R.toCx3 F).jR A3.fam3.F.μ0
          ((A3.fam3.F.R A3.fam3.F.μ0).toF ℓ ((R.toCx3 F).Z A3.fam3.F.μ0) y))) ∈ R.EEp3 p := h1
      rw [hp] at h3
      have h5 := (Submodule.mem_bot ℂ).1 h3
      exact h5
    have h4 := CxData.theta_jR_inj (R.toCx3 F) kR _ _ (coordinates_mem_subspace ℓ _ y) h2
    exact BlockDat.toF_injective _ ℓ _ (h4.trans (map_zero _).symm)
  rw [eq_bot_iff]
  intro y hy
  rw [Submodule.mem_bot]
  cases b
  · exact key _ y hy
  · exact key _ y hy

end GlobalTheory.Mem.R3

end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

noncomputable section

namespace GlobalTheory.CongConjugate

open ReciprocityTheory.Aut Formalism.AUTREP

theorem congConj : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ), principalLevelFrame.CongConj L n := by
  intro L _ _ _ n h N hN
  obtain ⟨d, hd, hdh⟩ := GlobalTheory.FinTypCount.exists_denom_matrix
    (((h.1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)))
  obtain ⟨e, he, heh⟩ := GlobalTheory.FinTypCount.exists_denom_matrix
    ((((h⁻¹).1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)))
  refine ⟨N * d * e, Nat.mul_pos (Nat.mul_pos hN hd) he, fun κ hκ => ?_⟩
  choose Y hY eY using hκ.2
  set H : Matrix (Fin n) (Fin n) (AL L) := ((h.1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) with hH
  set Hi : Matrix (Fin n) (Fin n) (AL L) := (((h⁻¹).1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) with hHi
  have hHH : Hi * H = 1 := by
    rw [hHi, hH, ← Units.val_mul, ← Subgroup.coe_mul, inv_mul_cancel]; rfl
  have hK : ((κ.1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) =
      1 + ((N * d * e : ℕ) : AL L) • Matrix.of Y := by
    ext a b
    have := eY a b
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]
    rw [← this]; ring
  have hprod : (((h⁻¹ * κ * h).1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) =
      Hi * (1 + ((N * d * e : ℕ) : AL L) • Matrix.of Y) * H := by
    rw [← hK]; simp [hHi, hH, Subgroup.coe_mul, Units.val_mul]
  set Z : Matrix (Fin n) (Fin n) (AL L) := ((e : AL L) • Hi) * Matrix.of Y * ((d : AL L) • H) with hZ
  have hZint : ∀ i j, Z i j ∈ ALint L := by
    intro i j
    rw [hZ, Matrix.mul_apply]
    refine Subring.sum_mem _ fun b _ => Subring.mul_mem _ ?_ ?_
    · rw [Matrix.mul_apply]
      refine Subring.sum_mem _ fun a _ => Subring.mul_mem _ ?_ (hY a b)
      simpa [Matrix.smul_apply, smul_eq_mul] using heh i a
    · simpa [Matrix.smul_apply, smul_eq_mul] using hdh b j
  have hdiff : Hi * (1 + ((N * d * e : ℕ) : AL L) • Matrix.of Y) * H - 1 = (N : AL L) • Z := by
    rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hHH, add_sub_cancel_left, hZ]
    rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul, smul_smul, smul_smul]
    congr 1
    push_cast; ring
  have hentry : ∀ i j, (((h⁻¹ * κ * h).1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) i j -
      (1 : Matrix (Fin n) (Fin n) (AL L)) i j = (N : AL L) * Z i j := by
    intro i j
    rw [hprod]
    have h2 := congrFun (congrFun hdiff i) j
    simpa [Matrix.sub_apply, Matrix.smul_apply] using h2
  refine ⟨fun i j => ?_, fun i j => ⟨Z i j, hZint i j, hentry i j⟩⟩
  have h3 : (((h⁻¹ * κ * h).1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) i j =
      (1 : Matrix (Fin n) (Fin n) (AL L)) i j + (N : AL L) * Z i j := by
    rw [← hentry]; ring
  rw [h3]
  refine add_mem ?_ (Subring.mul_mem _ (natCast_mem _ _) (hZint i j))
  rw [Matrix.one_apply]; split_ifs
  · exact one_mem _
  · exact zero_mem _

end GlobalTheory.CongConjugate
end
end

section

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host GlobalTheory.NT GlobalTheory.Published GlobalTheory.Mem GlobalTheory.Mem.Fld
open scoped nonZeroDivisors IntermediateField

namespace GlobalTheory.Mem.ValPow

variable {L : Type} [Field L] [NumberField L]

theorem count_span_int (w : HeightOneSpectrum (𝓞 L)) (a : 𝓞 L) (ha : a ≠ 0) :
    FractionalIdeal.count L w (FractionalIdeal.spanSingleton (𝓞 L)⁰ (algebraMap (𝓞 L) L a)) =
      -WithZero.log (w.valuation L (algebraMap (𝓞 L) L a)) := by
  classical
  rw [← FractionalIdeal.coeIdeal_span_singleton, FractionalIdeal.count_coe L w (by simpa using ha),
    HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_if_neg _ ha]
  simp

theorem ordF_eq_count (w : HeightOneSpectrum (𝓞 L)) (k : Lˣ) :
    ordF w k = FractionalIdeal.count L w (FractionalIdeal.spanSingleton (𝓞 L)⁰ (k : L)) := by
  obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (A := 𝓞 L) (k : L)
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact k.ne_zero (by rw [← hab]; simp)
  have ha' : algebraMap (𝓞 L) L a ≠ 0 := by simpa using ha0
  have hb' : algebraMap (𝓞 L) L b ≠ 0 := by simpa using hb0
  unfold ordF
  rw [← hab, div_eq_mul_inv, ← FractionalIdeal.spanSingleton_mul_spanSingleton, ← FractionalIdeal.spanSingleton_inv,
    FractionalIdeal.count_mul L w (FractionalIdeal.spanSingleton_ne_zero_iff.2 ha')
      (inv_ne_zero (FractionalIdeal.spanSingleton_ne_zero_iff.2 hb')),
    FractionalIdeal.count_inv, count_span_int w a ha0, count_span_int w b hb0, map_mul, map_inv₀,
    WithZero.log_mul ((Valuation.ne_zero_iff _).2 ha') (inv_ne_zero ((Valuation.ne_zero_iff _).2 hb')), WithZero.log_inv]
  ring

theorem locK_eq_one {χ : HChar L} {w : HeightOneSpectrum (𝓞 L)} (h : χ.TameAt w) (k : Lˣ)
    (hk : w.valuation L ((k : L) - 1) < 1) : χ.locK w k = 1 := by
  refine h _ ?_ ?_
  · unfold IsUnitAt
    have h1 : Valued.v ((atFin w k : (w.adicCompletion L)ˣ) : w.adicCompletion L) = w.valuation L (k : L) :=
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w (k : L)
    rw [h1]
    have := (w.valuation L).map_one_add_of_lt hk
    rwa [add_sub_cancel] at this
  · have h1 : ((atFin w k : (w.adicCompletion L)ˣ) : w.adicCompletion L) - 1 =
        algebraMap L (w.adicCompletion L) ((k : L) - 1) := by
      rw [map_sub, map_one]
      rfl
    have h2 : Valued.v (algebraMap L (w.adicCompletion L) ((k : L) - 1)) =
        w.valuation L ((k : L) - 1) := HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w _
    rw [h1, h2]
    rcases eq_or_ne (w.valuation L ((k : L) - 1)) 0 with h0 | h0
    · rw [h0]; exact zero_le
    · rw [← WithZero.exp_log h0, ← WithZero.exp_zero, WithZero.exp_lt_exp] at hk
      rw [← WithZero.exp_log h0, WithZero.exp_le_exp]
      push_cast
      omega

theorem inf_mul_val_pow : ∀ (L : Type) [Field L] [NumberField L] (χ : HChar L) (S : Finset (HeightOneSpectrum (𝓞 L))), (∀ w, w ∉ S → χ.UnrAt w) → (∀ w ∈ S, χ.TameAt w) → ∀ (v : HeightOneSpectrum (𝓞 L)), v ∉ S → ∀ (h : ℕ) (k : Lˣ), FractionalIdeal.spanSingleton (𝓞 L)⁰ (k : L) = (v.asIdeal : FractionalIdeal (𝓞 L)⁰ L) ^ h → (∀ w ∈ S, w.valuation L ((k : L) - 1) < 1) → χ.inf k * χ.val v ^ h = 1 := by
  classical
  intro L _ _ χ S hS hT v hv h k hk h1
  rw [← GlobalTheory.HeckeProduct.hchar_productRule L χ S hS k,
    Finset.prod_eq_one (fun w hw => locK_eq_one (hT w hw) k (h1 w hw)), mul_one]
  congr 1
  rw [finprod_eq_single _ v]
  · rw [finprod_eq_if, if_pos hv, ordF_eq_count, hk, FractionalIdeal.count_pow, FractionalIdeal.count_self, mul_one,
      zpow_natCast]
  · intro w hw
    rw [ordF_eq_count, hk, FractionalIdeal.count_pow, FractionalIdeal.count_maximal_coprime L w (Ne.symm hw), mul_zero,
      zpow_zero, finprod_one]

end GlobalTheory.Mem.ValPow

end
end
