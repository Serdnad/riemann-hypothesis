module

public import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
import Formalism.LocalToGlobal.Divisibility.RowLatLemmas
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open Matrix
open scoped Matrix

noncomputable section

namespace Formalism.IndefR.Links.EvTie

open Formalism.L2.DIV Formalism.IndefR.Cx

section Block

variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 : Type}

theorem dot_eq (S : CSD K) (u w : Fin S.dim → K) :
    S.csum (S.I u) (S.I w) = star u ⬝ᵥ S.H *ᵥ w := by

  simp only [CSD.csum, CSD.I, CSD.H, LinearMap.comp_apply, LinearEquiv.coe_coe, Module.Basis.equivFun_symm_apply,
  Submodule.subtype_apply, Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply, map_sum,
  map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, dotProduct, mulVec, Matrix.of_apply, Finset.mul_sum,
  Finset.sum_mul, smul_eq_mul, starRingEnd_apply, RingHom.id_apply]
  conv_lhs => rw [Finset.sum_comm]; enter [2, j]; rw [Finset.sum_comm]
  conv_lhs => rw [Finset.sum_comm]
  refine Fintype.sum_congr _ _ fun i => Fintype.sum_congr _ _ fun j => Fintype.sum_congr _ _ fun c => ?_
  rw [Pi.star_apply]
  ring

theorem proj_key (B : BlockDat K G Pl0) (ℓ : Lvl K G) (Z : Submodule K B.S.Forms)
    (hdet : IsUnit (B.HZ ℓ Z).det) :
    ((B.vE ℓ * B.zE ℓ Z)ᴴ * B.S.H * B.vE ℓ) * (B.zE ℓ Z * B.Pq ℓ Z) =
      (B.vE ℓ * B.zE ℓ Z)ᴴ * B.S.H * B.vE ℓ := by
  have hc : (Nat.card ℓ.P : K) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have hM : (B.vE ℓ)ᴴ * B.S.H * B.vE ℓ = (Nat.card ℓ.P : K) • B.HV ℓ := by
    simp only [BlockDat.HV, BlockDat.vE, CSD.goodPartHermitianForm, CSD.cutH, CSD.V0E, smul_smul, mul_inv_cancel₀ hc, one_smul]
  have hinv : B.HZ ℓ Z * (B.HZ ℓ Z)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hdet
  calc ((B.vE ℓ * B.zE ℓ Z)ᴴ * B.S.H * B.vE ℓ) * (B.zE ℓ Z * B.Pq ℓ Z)
      = (B.zE ℓ Z)ᴴ * ((B.vE ℓ)ᴴ * B.S.H * B.vE ℓ) * B.zE ℓ Z * B.Pq ℓ Z := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = (Nat.card ℓ.P : K) • (B.HZ ℓ Z * (B.HZ ℓ Z)⁻¹ * ((B.zE ℓ Z)ᴴ * B.HV ℓ)) := by
        rw [hM]
        simp only [BlockDat.HZ, BlockDat.Pq, orthPr, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
    _ = (B.vE ℓ * B.zE ℓ Z)ᴴ * B.S.H * B.vE ℓ := by
        rw [hinv, Matrix.one_mul, Matrix.conjTranspose_mul,
          show (B.zE ℓ Z)ᴴ * (B.vE ℓ)ᴴ * B.S.H * B.vE ℓ = (B.zE ℓ Z)ᴴ * ((B.vE ℓ)ᴴ * B.S.H * B.vE ℓ) by
            simp only [Matrix.mul_assoc], hM, Matrix.mul_smul]

theorem dot_key (B : BlockDat K G Pl0) (ℓ : Lvl K G) (Z : Submodule K B.S.Forms) (x : Fin (B.dZ ℓ Z) → K)
    (w : Fin (B.nV ℓ) → K) :
    star ((B.vE ℓ) *ᵥ ((B.zE ℓ Z) *ᵥ x)) ⬝ᵥ B.S.H *ᵥ ((B.vE ℓ) *ᵥ w) =
      star x ⬝ᵥ (((B.vE ℓ * B.zE ℓ Z)ᴴ * B.S.H * B.vE ℓ) *ᵥ w) := by
  rw [Matrix.mulVec_mulVec, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec]
  simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]

theorem evTie_block (B : BlockDat K G Pl0) (ℓ : Lvl K G) (Z : Submodule K B.S.Forms)
    (hdet : IsUnit (B.HZ ℓ Z).det) (x : Fin (B.dZ ℓ Z) → K) (y : Fin (B.nV ℓ) → K) :
    CSDForm.csumForm B.S (B.toF ℓ Z x) (B.S.basis.equivFun.symm ((B.vE ℓ) *ᵥ y)) =
      CSDForm.csumForm B.S (B.toF ℓ Z x) (B.toF ℓ Z ((B.Pq ℓ Z) *ᵥ y)) := by
  have key : ∀ a b : Fin B.S.dim → K, CSDForm.csumForm B.S (B.S.basis.equivFun.symm a)
      (B.S.basis.equivFun.symm b) = star a ⬝ᵥ B.S.H *ᵥ b := fun a b => dot_eq B.S a b
  have hT : ∀ v, B.toF ℓ Z v = B.S.basis.equivFun.symm (B.vE ℓ *ᵥ (B.zE ℓ Z *ᵥ v)) := fun v => rfl
  rw [hT, hT, key, key, dot_key, dot_key, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
    Matrix.mul_assoc ((B.vE ℓ * B.zE ℓ Z)ᴴ * B.S.H * B.vE ℓ), proj_key B ℓ Z hdet]

end Block

section Face

open Formalism.BasicNotions Formalism.IndefR.Links

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem evTie_of_det {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type}
    {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} (F : Face3 D A3) (X : CxData A3.fam3.amb3)
    (hdet : ∀ t, IsUnit ((A3.A.fam.R t).HZ (A3.A.fam.lvl F.P1 F.ψ1) (X.zs.Z t)).det) :
    X.EVTie F.cr F.cv (F.eV X.zs) := by
  refine ⟨fun t y => ⟨y, rfl⟩, fun t y x => ?_⟩
  exact evTie_block (A3.A.fam.R t) (A3.A.fam.lvl F.P1 F.ψ1) (X.zs.Z t) (hdet t) x y

end Face

section Ok

open Formalism.BasicNotions Formalism.IndefR.Links

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem evTie_of_ok {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type}
    {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {s : ℕ} (hOk : A3.fam3.Ok3 s) (F : Face3 D A3)
    (X : CxData A3.fam3.amb3) : X.EVTie F.cr F.cv (F.eV X.zs) :=
  evTie_of_det F X fun t =>
    BlockDat.HZ_det hOk.ok2.conj (hOk.ok2.what₂ t) (fun χ hχ => hOk.ok2.irr χ hχ)

theorem evTie_real {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type}
    {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
    (hOk : ∃ s, A3.fam3.Ok3 s) (R : RealDat3 D A3 Ks) (F : Face3 D A3) :
    (R.toCx3 F).EVTie F.cr F.cv (F.eV (R.toCx3 F).zs) := by
  obtain ⟨s, hs⟩ := hOk
  exact evTie_of_ok hs F (R.toCx3 F)

end Ok

end Formalism.IndefR.Links.EvTie

end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open scoped TensorProduct InnerProductSpace

namespace Formalism.IndefR.Links

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

section Err

open Formalism.IndefR.Cx

variable {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

namespace RealDat3

def withErr (R : RealDat3 D A3 Ks) (e : type_of% R.err0) : RealDat3 D A3 Ks :=
  { R with toRealDat := { R.toRealDat with err0 := e } }

variable {R : RealDat3 D A3 Ks} {F : Face3 D A3}

def _root_.Formalism.IndefR.Links.reErr {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K} {Am : DefAmb Bs}
    (X : CxData Am) (e : type_of% X.err0) : CxData Am := { X with err0 := e }

theorem partAt_withErr (e i p v) : (R.withErr e).PartAt F i p v ↔ R.PartAt F i p v := by
  exact Iff.rfl

theorem zs_withErr (e) : ((R.withErr e).toCx3 F).zs = (R.toCx3 F).zs := by
  rfl



theorem weak_characterisation_with_error (h : R.WeakCharacterisation F) (e) : (R.withErr e).WeakCharacterisation F := by
  cases_type* RealDat3.WeakCharacterisation RealDat.BaseW RealDat.IsGrp RealDat.IsFam RealDat.IsModels RealDat.IsChainW RealDat.IsThPW RealDat3.IsInert RealDat3.IsScal RealDat3.IsTup
  repeat' (first | assumption | constructor)

end RealDat3

end Err

section Three

open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.WeilFull Formalism.IndefR.Fin Formalism.IndefR.Eqv

variable {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {F : Face3 D A3}

namespace RealDat3

variable (R : RealDat3 D A3 Ks)

def updS (kap : ℝ) (lam : type_of% R.lam3) : RealDat3 D A3 Ks :=
  { R with toRealDat := R.toRealDat.upd6 kap R.lam, lam3 := lam }

def Eig0 (i : Fin D.R.m) (t : T) (p : A3.fam3.base3.Ix) (l : ℝ) : Prop :=
  R.Wp3 i p ≠ ⊥ ∧ ∀ x ∈ R.Wp3 i p, R.thG i t (LinearMap.adjoint (R.thG i t) x) = (l : ℂ) • x


variable (F) in
def EigOff (i : Fin D.R.m) (p : A3.fam3.base3.Ix) (v : InfinitePlace D.what₂.LL) (l : ℝ) : Prop :=
  PartX F.cr (R.toCx3 F) false i p v ∧ SimX F.cr (R.toCx3 F) false i p v l

variable {R}

theorem base_eigenvalue_unique {i t p} (l l' : ℝ) (h : R.Eig0 i t p l) (h' : R.Eig0 i t p l') : l = l' := by
  obtain ⟨hb, hl⟩ := h
  obtain ⟨-, hl'⟩ := h'
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hb
  have hxx : (l : ℂ) • x = (l' : ℂ) • x := (hl x hx).symm.trans (hl' x hx)
  have hc : (l : ℂ) = (l' : ℂ) := by
    by_contra hne
    apply hx0
    have hne' : (l : ℂ) - (l' : ℂ) ≠ 0 := sub_ne_zero.mpr hne
    have h0 : ((l : ℂ) - (l' : ℂ)) • x = 0 := by rw [sub_smul, hxx, sub_self]
    calc x = ((l : ℂ) - (l' : ℂ))⁻¹ • (((l : ℂ) - (l' : ℂ)) • x) := by
          rw [smul_smul, inv_mul_cancel₀ hne', one_smul]
      _ = 0 := by rw [h0, smul_zero]
  exact_mod_cast hc

theorem eigOff_unique {i p v} (l l' : ℝ) (h : R.EigOff F i p v l) (h' : R.EigOff F i p v l') : l = l' := by
  obtain ⟨⟨x, hx, hm⟩, hs⟩ := h
  obtain ⟨-, hs'⟩ := h'
  have e1 := hs x hx x
  have e2 := hs' x hx x
  have hc : ((l : ℝ) : ℂ) = ((l' : ℝ) : ℂ) := mul_right_cancel₀ hm (e1.symm.trans e2)
  exact_mod_cast hc

theorem partAt_updS (kap lam i p v) : (R.updS kap lam).PartAt F i p v ↔ PartX F.cr (R.toCx3 F) false i p v := by
  exact Iff.rfl

theorem sim_updS (kap lam i p v l) : SimX F.cr ((R.updS kap lam).toCx3 F) false i p v l ↔ SimX F.cr (R.toCx3 F) false i p v l := by
  exact Iff.rfl

theorem zs_updS (kap lam) : ((R.updS kap lam).toCx3 F).zs = (R.toCx3 F).zs := by
  rfl

end RealDat3


open Classical in
theorem scalars_exist (R : RealDat3 D A3 Ks) : ∃ kap lam, (R.updS kap lam).IsScal F := by

  have hcan : ∀ {N : Type} [AddCommGroup N] [Module ℂ N] {a b : ℂ} {x : N}, x ≠ 0 → a • x = b • x → a = b := by
    intro N _ _ a b x hx h
    by_contra hne
    apply hx
    have hne' : a - b ≠ 0 := sub_ne_zero.mpr hne
    have h0 : (a - b) • x = 0 := by rw [sub_smul, h, sub_self]
    calc x = (a - b)⁻¹ • ((a - b) • x) := by rw [smul_smul, inv_mul_cancel₀ hne', one_smul]
      _ = 0 := by rw [h0, smul_zero]

  obtain ⟨lam, hlam⟩ : ∃ lam : Fin D.R.m → T → A3.fam3.base3.Ix → InfinitePlace D.what₂.LL → ℝ,
      ∀ i t p v, lam i t p v =
        if v = A3.A.v0 then
          (if h : ∃ l, R.Eig0 i t p l then h.choose else Real.exp ((F.Zsc (R.toCx3 F).zs).l6m i))
        else
          (if h : ∃ l, R.EigOff F i p v l then h.choose else Real.exp ((F.Zsc (R.toCx3 F).zs).l6m i)) :=
    ⟨_, fun _ _ _ _ => rfl⟩

  obtain ⟨kap, hkap⟩ : ∃ kap : ℝ, ∀ κ : ℝ,
      Lift.IsKap D.R.m (fun t => R.Th t ∘ₗ LinearMap.adjoint (R.Th t)) R.EEp3 (R.updS 0 lam).lamN κ →
      (∃ t p, R.EEp3 p ≠ ⊥ ∧ ∏ j ∈ Finset.Icc 1 D.R.m, (R.updS 0 lam).lamN t j p ≠ 0) → kap = κ := by
    by_cases hex : ∃ κ : ℝ,
        Lift.IsKap D.R.m (fun t => R.Th t ∘ₗ LinearMap.adjoint (R.Th t)) R.EEp3 (R.updS 0 lam).lamN κ ∧
        (∃ t p, R.EEp3 p ≠ ⊥ ∧ ∏ j ∈ Finset.Icc 1 D.R.m, (R.updS 0 lam).lamN t j p ≠ 0)
    · obtain ⟨κ0, hk0, -⟩ := hex
      refine ⟨κ0, fun κ hk hnd => ?_⟩
      obtain ⟨t, p, hE, hP⟩ := hnd
      obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hE
      have e := hcan hx0 ((hk0 t p x hx).symm.trans (hk t p x hx))
      have e' : κ0 * ∏ j ∈ Finset.Icc 1 D.R.m, (R.updS 0 lam).lamN t j p =
          κ * ∏ j ∈ Finset.Icc 1 D.R.m, (R.updS 0 lam).lamN t j p := by exact_mod_cast e
      exact mul_right_cancel₀ hP e'
    · exact ⟨0, fun κ hk hnd => absurd ⟨κ, hk, hnd⟩ hex⟩
  refine ⟨kap, lam, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · intro i t p l hb hl
    have hE : R.Eig0 i t p l := ⟨hb, hl⟩
    show lam i t p A3.A.v0 = l
    rw [hlam, if_pos rfl, dite_eq_left ⟨l, hE⟩]
    exact RealDat3.base_eigenvalue_unique (R := R) _ _ (Exists.choose_spec _) hE
  · intro κ hk hnd
    exact hkap κ hk hnd
  · intro i p v l hv hP hS
    have hPX : PartX F.cr (R.toCx3 F) false i p v := (RealDat3.partAt_updS kap lam i p v).1 hP
    have hSX : SimX F.cr (R.toCx3 F) false i p v l := (RealDat3.sim_updS kap lam i p v l).1 hS
    have hE : R.EigOff F i p v l := ⟨hPX, hSX⟩
    show lam i A3.A.μ0 p v = l
    rw [hlam, if_neg hv, dite_eq_left ⟨l, hE⟩]
    exact RealDat3.eigOff_unique (R := R) _ _ (Exists.choose_spec _) hE
  · intro i t p hb
    show lam i t p A3.A.v0 = Real.exp ((F.Zsc ((R.updS kap lam).toCx3 F).zs).l6m i)
    rw [RealDat3.zs_updS, hlam, if_pos rfl, dite_eq_right]
    rintro ⟨l, hl⟩
    exact hl.1 hb
  · intro i p v hv hnP
    show lam i A3.A.μ0 p v = Real.exp ((F.Zsc ((R.updS kap lam).toCx3 F).zs).l6m i)
    rw [RealDat3.zs_updS, hlam, if_neg hv, dite_eq_right]
    rintro ⟨l, hl⟩
    exact hnP ((RealDat3.partAt_updS kap lam i p v).2 hl.1)
  · intro i t p v hv
    show lam i t p v = lam i A3.A.μ0 p v
    rw [hlam, hlam, if_neg hv, if_neg hv]


end Three

end Formalism.IndefR.Links

end
end
