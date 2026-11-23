module

public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.HodgeWedgeFields.H1CommutesBaseChange
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle026
public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.ColMatMulGlEmbMat
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.LeibnizDerivatives.EPGFalseEqLastIff
public import Development.WeilBound.RepresentationTheoryGL.HolomorphicDiscreteSeries.EmbeddedFrames.PfD
public import Formalism.RealPlaceAnalysis.Bundle001
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle130
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
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.LeibnizOrders.ProdGPn

@[expose] public section

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.Axis

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.Axis

theorem mp_box_tmul {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R) {a a' b b' : C}
    (φ : a ⟶ a') (ψ : b ⟶ b') (u : F.obj a) (v : F.obj b) :
    mp (box F) (show ((a, b) : C × C) ⟶ (a', b') from (φ, ψ)) (u ⊗ₜ[R] v) = mp F φ u ⊗ₜ[R] mp F ψ v :=
  rfl

theorem exists_pull_of_vanish_fst (R : Type) [CommRing R] (C : Type) [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R)
    (hU : USt F) (f : Z1 (box F))
    (hf : ∀ (a a' b : C) (φ : a ⟶ a'), f.1 (a, b) (a', b) (φ, 𝟙 b) = 0) :
    ∃ y : Z1 F, (boxR F).pullbackOneCocycle y = f := by

  have hk : ∀ {b b' : C} (ψ : b ⟶ b') {a a' : C} (φ : a ⟶ a'),
      f.1 (a', b) (a', b') (𝟙 a', ψ) =
        mp (box F) (show ((a, b') : C × C) ⟶ (a', b') from (φ, 𝟙 b'))
          (f.1 (a, b) (a, b') (𝟙 a, ψ)) := by
    intro b b' ψ a a' φ
    have e1 := Z1.comp f (T := (a, b)) (T' := (a', b)) (T'' := (a', b'))
      (φ, 𝟙 b) (𝟙 a', ψ)
    have e2 := Z1.comp f (T := (a, b)) (T' := (a, b')) (T'' := (a', b'))
      (𝟙 a, ψ) (φ, 𝟙 b')
    have e : (show ((a, b) : C × C) ⟶ (a', b) from (φ, 𝟙 b)) ≫
        (show ((a', b) : C × C) ⟶ (a', b') from (𝟙 a', ψ)) =
        (show ((a, b) : C × C) ⟶ (a, b') from (𝟙 a, ψ)) ≫
        (show ((a, b') : C × C) ⟶ (a', b') from (φ, 𝟙 b')) := by
      simp
    rw [e, e2, hf a a' b' φ, add_zero, hf a a' b φ, map_zero, zero_add] at e1
    exact e1.symm
  have hcomm : ∀ {a a' b' : C} (φ : a ⟶ a') (x : F.obj a ⊗[R] F.obj b'),
      TensorProduct.comm R (F.obj a') (F.obj b')
          (mp (box F) (show ((a, b') : C × C) ⟶ (a', b') from (φ, 𝟙 b')) x) =
        (mp F φ).toLinearMap.lTensor (F.obj b') (TensorProduct.comm R (F.obj a) (F.obj b') x) := by
    intro a a' b' φ x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul u v => rw [mp_box_tmul, mp_id]; simp
    | add u v hu hv => simp only [map_add (f := _), hu, hv]

  have hex : ∀ {b b' : C} (ψ : b ⟶ b'), ∃! m : F.obj b', ∀ a : C,
      f.1 (a, b) (a, b') (𝟙 a, ψ) = (1 : F.obj a) ⊗ₜ[R] m := by
    intro b b' ψ
    obtain ⟨m, hm, hu⟩ := hU (F.obj b')
      (fun a ↦ TensorProduct.comm R (F.obj a) (F.obj b') (f.1 (a, b) (a, b') (𝟙 a, ψ)))
      (fun a a' φ ↦ by rw [hk ψ φ, hcomm])
    have hiff : ∀ (a : C) (m' : F.obj b'),
        TensorProduct.comm R (F.obj a) (F.obj b') (f.1 (a, b) (a, b') (𝟙 a, ψ)) = m' ⊗ₜ[R] (1 : F.obj a) ↔
          f.1 (a, b) (a, b') (𝟙 a, ψ) = (1 : F.obj a) ⊗ₜ[R] m' := by
      intro a m'
      exact (TensorProduct.comm R (F.obj a) (F.obj b')).injective.eq_iff' (TensorProduct.comm_tmul R _ _ _ _)
    exact ⟨m, fun a ↦ (hiff a m).1 (hm a), fun m' h ↦ hu m' fun a ↦ (hiff a m').2 (h a)⟩
  choose y hy huniq using @hex
  refine ⟨⟨fun b b' ψ ↦ y ψ, fun b b' b'' ψ χ ↦ ?_⟩, ?_⟩
  · refine (huniq (ψ ≫ χ) _ fun a ↦ ?_).symm
    have e := Z1.comp f (T := (a, b)) (T' := (a, b')) (T'' := (a, b''))
      (𝟙 a, ψ) (𝟙 a, χ)
    have e' : (show ((a, b) : C × C) ⟶ (a, b') from (𝟙 a, ψ)) ≫
        (show ((a, b') : C × C) ⟶ (a, b'') from (𝟙 a, χ)) = (𝟙 a, ψ ≫ χ) := by
      simp
    rw [e', hy ψ a, hy χ a] at e
    refine e.trans ?_
    rw [mp_box_tmul, mp_id, TensorProduct.tmul_add]
  · refine Subtype.ext ?_
    funext T T' φ
    obtain ⟨a, b⟩ := T
    obtain ⟨a', b'⟩ := T'
    obtain ⟨φ₁, φ₂⟩ := φ
    have e := Z1.comp f (T := (a, b)) (T' := (a', b)) (T'' := (a', b'))
      (φ₁, 𝟙 b) (𝟙 a', φ₂)
    have e' : (show ((a, b) : C × C) ⟶ (a', b) from (φ₁, 𝟙 b)) ≫
        (show ((a', b) : C × C) ⟶ (a', b') from (𝟙 a', φ₂)) = (φ₁, φ₂) := by
      simp
    rw [e', hf a a' b φ₁, map_zero, zero_add, hy φ₂ a'] at e
    exact e.symm

end GlobalTheory.CompanionTheory.Axis
end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory GlobalTheory.CatCoh MainStatements.Hodge

namespace GlobalTheory.CompanionTheory.HodgeCx

variable {R : Type} [CommRing R] {C D : Type} [Category.{0} C] [Category.{0} D]

section Act

variable (F : C ⥤ CommAlgCat.{0} R)

def act {m n : ℕ} (θ : Fin (m + 1) →o Fin (n + 1)) : Cn F m →ₗ[R] Cn F n :=
  LinearMap.pi fun c ↦ (mp F (c.map (homOfLE (Fin.le_last (θ (Fin.last m)))))).toLinearMap ∘ₗ
    LinearMap.proj (R := R) (φ := fun c : Fin (m + 1) ⥤ C ↦ (F.obj (c.obj (Fin.last m)) : Type))
      (θ.monotone.functor ⋙ c)

theorem act_apply {m n : ℕ} (θ : Fin (m + 1) →o Fin (n + 1)) (f : Cn F m) (c : Fin (n + 1) ⥤ C) :
    act F θ f c = mp F (c.map (homOfLE (Fin.le_last (θ (Fin.last m))))) (f (θ.monotone.functor ⋙ c)) :=
  rfl

private theorem mp_map_endo_apply {n : ℕ} (c : Fin (n + 1) ⥤ C) {x : Fin (n + 1)} (h : x ⟶ x)
    (b : F.obj (c.obj x)) : GlobalTheory.CatCoh.mp F (c.map h) b = b := by
  have hc : c.map h = 𝟙 (c.obj x) := by
    rw [Subsingleton.elim h (𝟙 x)]
    exact c.map_id x
  rw [hc, GlobalTheory.CatCoh.mp_id]

private theorem mp_map_comp_apply {n : ℕ} (c : Fin (n + 1) ⥤ C) {x y z : Fin (n + 1)}
    (h : x ⟶ z) (h₁ : x ⟶ y) (h₂ : y ⟶ z) (b : F.obj (c.obj x)) :
    GlobalTheory.CatCoh.mp F (c.map h) b =
      GlobalTheory.CatCoh.mp F (c.map h₂) (GlobalTheory.CatCoh.mp F (c.map h₁) b) := by
  rw [Subsingleton.elim h (h₁ ≫ h₂), Functor.map_comp, GlobalTheory.CatCoh.mp_comp]

theorem act_id {n : ℕ} (f : Cn F n) : act F (OrderHom.id : Fin (n + 1) →o Fin (n + 1)) f = f := by
  funext c
  show GlobalTheory.CatCoh.mp F (c.map (𝟙 (Fin.last n))) (f c) = f c
  exact mp_map_endo_apply F c _ _

theorem act_comp {k m n : ℕ} (θ : Fin (k + 1) →o Fin (m + 1)) (ψ : Fin (m + 1) →o Fin (n + 1))
    (f : Cn F k) : act F (ψ.comp θ) f = act F ψ (act F θ f) := by
  funext c
  exact mp_map_comp_apply F c _
    (homOfLE (ψ.monotone (Fin.le_last (θ (Fin.last k))))) (homOfLE (Fin.le_last (ψ (Fin.last m))))
    (f ((ψ.comp θ).monotone.functor ⋙ c))

def cosimp : CosimplicialObject (ModuleCat.{0} R) where
  obj a := ModuleCat.of R (Cn F a.len)
  map θ := ModuleCat.ofHom (act F θ.toOrderHom)
  map_id a := ModuleCat.hom_ext (LinearMap.ext fun f ↦ act_id F f)
  map_comp θ ψ := ModuleCat.hom_ext (LinearMap.ext fun f ↦ act_comp F θ.toOrderHom ψ.toOrderHom f)

theorem cof_eq (n : ℕ) (i : Fin (n + 2)) :
    cof F n i = act F (Fin.succAboveOrderEmb i).toOrderHom := rfl

theorem objD_hom (n : ℕ) : (AlgebraicTopology.AlternatingCofaceMapComplex.objD (cosimp F) n).hom = dn F n := by
  unfold AlgebraicTopology.AlternatingCofaceMapComplex.objD
  rw [ModuleCat.hom_sum, MainStatements.Hodge.dn]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [ModuleCat.hom_zsmul]
  first
  | rfl
  | (rw [← Int.cast_smul_eq_zsmul R, Int.cast_pow, Int.cast_neg, Int.cast_one]; rfl)

theorem dn_comp_dn (n : ℕ) : dn F (n + 1) ∘ₗ dn F n = 0 := by
  have h := congrArg ModuleCat.Hom.hom
    (AlgebraicTopology.AlternatingCofaceMapComplex.d_squared (GlobalTheory.CompanionTheory.HodgeCx.cosimp F) n)
  rw [ModuleCat.hom_comp, GlobalTheory.CompanionTheory.HodgeCx.objD_hom, GlobalTheory.CompanionTheory.HodgeCx.objD_hom,
    ModuleCat.hom_zero] at h
  exact h

end Act

theorem pulln_cof {F : C ⥤ CommAlgCat.{0} R} {G : D ⥤ CommAlgCat.{0} R}
    (m : CoefMap (RingHom.id R) F G) (n : ℕ) (i : Fin (n + 2)) (f : Cn F n) :
    pulln m (n + 1) (cof F n i f) = cof G n i (pulln m n f) := by
  funext c
  exact m.3 (c.map (homOfLE (Fin.le_last _))) (f (MainStatements.Hodge.face i c ⋙ m.1))

theorem pulln_dn {F : C ⥤ CommAlgCat.{0} R} {G : D ⥤ CommAlgCat.{0} R}
    (m : CoefMap (RingHom.id R) F G) (n : ℕ) :
    pulln m (n + 1) ∘ₗ dn F n = dn G n ∘ₗ pulln m n := by
  apply LinearMap.ext
  intro f

  simp only [LinearMap.comp_apply, MainStatements.Hodge.dn, LinearMap.sum_apply,
  LinearMap.smul_apply, map_sum, map_smul, map_zsmul, GlobalTheory.CompanionTheory.HodgeCx.pulln_cof]

theorem cxSt : CxSt := by
  intro R _ C _ F
  exact ⟨GlobalTheory.CompanionTheory.HodgeCx.dn_comp_dn F, fun D _ G m n => GlobalTheory.CompanionTheory.HodgeCx.pulln_dn m n⟩

end GlobalTheory.CompanionTheory.HodgeCx
end
end

section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib

noncomputable section

namespace GlobalTheory.CompanionTheory.BZMir.GpExists

section Entries

variable {k : Type} [Field k]

theorem unip_apply_of_ne_last (n : ℕ) (v : Multiplicative (Fin n → k)) (p q : Fin (n + 1)) (hq : q ≠ Fin.last n) :
    ((unip k n v : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) p q =
      (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) k) p q := by
  show (1 + GlobalTheory.BZMir.colMat k n (Multiplicative.toAdd v)) p q = _
  simp [GlobalTheory.BZMir.colMat, hq]

theorem unip_apply_last_last (n : ℕ) (v : Multiplicative (Fin n → k)) :
    ((unip k n v : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (Fin.last n) (Fin.last n) = 1 := by
  show (1 + GlobalTheory.BZMir.colMat k n (Multiplicative.toAdd v)) (Fin.last n) (Fin.last n) = 1
  simp [GlobalTheory.BZMir.colMat]

end Entries

theorem blockIndex_false_val (m j : ℕ) (a : Fin m) : (eGP m j ⟨false, a⟩ : Fin (m + j + 1)).val = a.val := by
  first
  | rfl
  | simp [GlobalTheory.BZMir.Leib.eGP, GlobalTheory.SmGL.stdSum]

theorem blockIndex_true_val (m j : ℕ) (b : Fin (j + 1)) : (eGP m j ⟨true, b⟩ : Fin (m + j + 1)).val = m + b.val := by
  first
  | rfl
  | simp [GlobalTheory.BZMir.Leib.eGP, GlobalTheory.SmGL.stdSum]

end GlobalTheory.CompanionTheory.BZMir.GpExists

namespace GlobalTheory.CompanionTheory.BZMir

open GpExists

theorem exists_gpProj_unip (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (m j : ℕ) (u : Mir k j) (hu : u ∈ MirUin k j) :
    ∃ v : MirabolicParabolic k m j, (v : Mir k (m + j)) ∈ MirUin k (m + j) ∧ gpProj k m j v = (1, u) := by
  have hu' : (u : GL (Fin (j + 1)) k) ∈ GlobalTheory.BZMir.MirU k j := by
    unfold GlobalTheory.BZMir.MirUin at hu
    exact Subgroup.mem_subgroupOf.1 hu
  unfold GlobalTheory.BZMir.MirU at hu'
  rw [MonoidHom.mem_range] at hu'
  obtain ⟨w, hw⟩ := hu'
  set v' : Multiplicative (Fin (m + j) → k) :=
    Multiplicative.ofAdd (Fin.append (0 : Fin m → k) (Multiplicative.toAdd w)) with hv'
  have hU : GlobalTheory.BZMir.unip k (m + j) v' ∈ GlobalTheory.BZMir.MirU k (m + j) := by
    unfold GlobalTheory.BZMir.MirU
    exact MonoidHom.mem_range.2 ⟨v', rfl⟩
  have hM : GlobalTheory.BZMir.unip k (m + j) v' ∈ GlobalTheory.BZMir.Mir k (m + j) :=
    GlobalTheory.BZMir.MirU_le_Mir k (m + j) hU
  have hP : (⟨GlobalTheory.BZMir.unip k (m + j) v', hM⟩ : GlobalTheory.BZMir.Mir k (m + j)) ∈
      GlobalTheory.BZMir.Leib.MirabolicParabolic k m j := by
    unfold GlobalTheory.BZMir.Leib.MirabolicParabolic
    rw [Subgroup.mem_comap]
    show GlobalTheory.BZMir.unip k (m + j) v' ∈ _
    refine (GlobalTheory.SmGL.mem_parab_two k).2 (fun b a => ?_)
    rw [GlobalTheory.CompanionTheory.BZMir.GpExists.unip_apply_of_ne_last]
    · exact Matrix.one_apply_ne (fun h => by simpa using Equiv.injective _ h)
    · exact GlobalTheory.BZMir.Leib.blockIndex_false_ne_last m j a
  refine ⟨⟨⟨GlobalTheory.BZMir.unip k (m + j) v', hM⟩, hP⟩, ?_, ?_⟩
  · unfold GlobalTheory.BZMir.MirUin
    exact Subgroup.mem_subgroupOf.2 hU
  apply Prod.ext
  · apply Units.ext
    ext a a'
    simp only [GlobalTheory.BZMir.Leib.gpProj, MonoidHom.prod_apply, MonoidHom.comp_apply,
      Pi.evalMonoidHom_apply]
    rw [GlobalTheory.SmGL.leviProj_apply]
    change ((GlobalTheory.BZMir.unip k (m + j) v' : GL (Fin (m + j + 1)) k) :
      Matrix (Fin (m + j + 1)) (Fin (m + j + 1)) k) _ _ = _
    rw [GlobalTheory.CompanionTheory.BZMir.GpExists.unip_apply_of_ne_last _ _ _ _ (GlobalTheory.BZMir.Leib.blockIndex_false_ne_last m j a')]
    by_cases h : a = a'
    · subst h
      simp
    · rw [Matrix.one_apply_ne ((GlobalTheory.BZMir.Leib.eGP m j).injective.ne (by simpa using h)),
        Units.val_one, Matrix.one_apply_ne h]
  · apply Subtype.ext
    apply Units.ext
    ext b b'
    first
    | (show ((GlobalTheory.SmGL.leviProj k (GlobalTheory.BZMir.Leib.eGP m j)
          (GlobalTheory.BZMir.Leib.hgpIncl k m j ⟨⟨GlobalTheory.BZMir.unip k (m + j) v', hM⟩, hP⟩) true :
          GL _ k) : Matrix _ _ k) b b' = _
       rw [GlobalTheory.SmGL.leviProj_apply])
    | (simp only [GlobalTheory.BZMir.Leib.gpProj, MonoidHom.prod_apply, MonoidHom.codRestrict_apply,
          MonoidHom.coe_codRestrict, MonoidHom.comp_apply, Pi.evalMonoidHom_apply, Subgroup.coe_mk]
       rw [GlobalTheory.SmGL.leviProj_apply])
    change ((GlobalTheory.BZMir.unip k (m + j) v' : GL (Fin (m + j + 1)) k) :
      Matrix (Fin (m + j + 1)) (Fin (m + j + 1)) k) _ _ = _
    rw [← hw]
    induction b' using Fin.lastCases with
    | last =>
      rw [GlobalTheory.BZMir.Leib.blockIndex_true_last]
      induction b using Fin.lastCases with
      | last =>
        rw [GlobalTheory.BZMir.Leib.blockIndex_true_last, GlobalTheory.CompanionTheory.BZMir.GpExists.unip_apply_last_last,
          GlobalTheory.CompanionTheory.BZMir.GpExists.unip_apply_last_last]
      | cast i =>
        have hidx : GlobalTheory.BZMir.Leib.eGP m j ⟨true, Fin.castSucc i⟩ = Fin.castSucc (Fin.natAdd m i) :=
          Fin.ext (by simp [GlobalTheory.CompanionTheory.BZMir.GpExists.blockIndex_true_val])
        rw [hidx, GlobalTheory.BZMir.unip_apply_castSucc_last, GlobalTheory.BZMir.unip_apply_castSucc_last, hv']
        simp
    | cast i =>
      have hne : GlobalTheory.BZMir.Leib.eGP m j ⟨true, Fin.castSucc i⟩ ≠ Fin.last (m + j) :=
        fun h => Fin.castSucc_ne_last i ((GlobalTheory.BZMir.Leib.blockIndex_true_eq_last_iff m j _).1 h)
      rw [GlobalTheory.CompanionTheory.BZMir.GpExists.unip_apply_of_ne_last _ _ _ _ hne,
        GlobalTheory.CompanionTheory.BZMir.GpExists.unip_apply_of_ne_last _ _ _ _ (Fin.castSucc_ne_last i)]
      by_cases h : b = Fin.castSucc i
      · subst h
        simp
      · rw [Matrix.one_apply_ne ((GlobalTheory.BZMir.Leib.eGP m j).injective.ne (by simpa using h)),
          Matrix.one_apply_ne h]

end GlobalTheory.CompanionTheory.BZMir

end
end

section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib

noncomputable section

namespace GlobalTheory.CompanionTheory.GpUnip

theorem mirUin_entry (k : Type) [Field k] (n : ℕ) (u : Mir k n) (hu : u ∈ MirUin k n)
    (a b : Fin (n + 1)) (hb : b ≠ Fin.last n) :
    ((u : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) a b =
      (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) k) a b := by
  obtain ⟨v, hv⟩ := MonoidHom.mem_range.mp (Subgroup.mem_subgroupOf.mp hu)
  rw [← hv]
  change (1 + GlobalTheory.BZMir.colMat k n (Multiplicative.toAdd v)) a b = _
  simp [GlobalTheory.BZMir.colMat, hb]

theorem gpProj_unip : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (m j : ℕ) (u : MirabolicParabolic k m j), (u : Mir k (m + j)) ∈ MirUin k (m + j) →
      (gpProj k m j u).1 = 1 ∧ (gpProj k m j u).2 ∈ MirUin k j := by
  intro k _ _ _ _ m j u hu
  have key : ∀ a b : Fin (m + j + 1), b ≠ Fin.last (m + j) →
      (((u : GlobalTheory.BZMir.Mir k (m + j)) : GL (Fin (m + j + 1)) k) :
        Matrix (Fin (m + j + 1)) (Fin (m + j + 1)) k) a b =
        (1 : Matrix (Fin (m + j + 1)) (Fin (m + j + 1)) k) a b :=
    fun a b hb => GlobalTheory.CompanionTheory.GpUnip.mirUin_entry k (m + j) _ hu a b hb
  have e_inj := (GlobalTheory.BZMir.Leib.eGP m j).injective
  constructor
  · ext i i'
    have h := GlobalTheory.SmGL.leviProj_apply k (GlobalTheory.BZMir.Leib.eGP m j)
      (GlobalTheory.BZMir.Leib.hgpIncl k m j u) false i i'
    refine h.trans ((key _ _ (GlobalTheory.BZMir.Leib.blockIndex_false_ne_last m j i')).trans ?_)
    simp only [Matrix.one_apply, e_inj.eq_iff, Sigma.mk.inj_iff, heq_eq_eq, true_and,
      Units.val_one]
  · have mem_of_proj (n : ℕ) (y : Mir k n) (hblock : ∀ i j : Fin n,
          ((y : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (Fin.castSucc i) (Fin.castSucc j) =
            (1 : Matrix (Fin n) (Fin n) k) i j) :
        y ∈ MirUin k n := by
      have hrow : ∀ j, ((y : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (Fin.last n) j =
          GlobalTheory.BZMir.eLast k n j :=
        fun j => congrFun ((GlobalTheory.BZMir.mem_Mir_iff k (y : GL (Fin (n + 1)) k)).1 y.2) j
      rw [GlobalTheory.BZMir.MirUin, Subgroup.mem_subgroupOf, GlobalTheory.BZMir.MirU,
        MonoidHom.mem_range]
      refine ⟨Multiplicative.ofAdd fun i =>
        ((y : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (Fin.castSucc i) (Fin.last n), ?_⟩
      apply Units.ext
      ext i j
      change ((1 : Matrix (Fin (n + 1)) (Fin (n + 1)) k) + GlobalTheory.BZMir.colMat k n (fun i =>
        ((y : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (Fin.castSucc i) (Fin.last n))) i j =
        ((y : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) i j
      rw [Matrix.add_apply, GlobalTheory.BZMir.colMat]
      rcases Fin.eq_castSucc_or_eq_last i with ⟨i, rfl⟩ | rfl <;>
        rcases Fin.eq_castSucc_or_eq_last j with ⟨j, rfl⟩ | rfl
      · simp [Matrix.one_apply, Fin.castSucc_ne_last, hblock]
      · simp [Matrix.one_apply, Fin.castSucc_ne_last]
      · simp [Matrix.one_apply, Fin.castSucc_ne_last, (Fin.castSucc_ne_last _).symm, hrow,
          GlobalTheory.BZMir.eLast]
      · simp [hrow, GlobalTheory.BZMir.eLast]
    apply mem_of_proj j _
    intro i i'
    have h := GlobalTheory.SmGL.leviProj_apply k (GlobalTheory.BZMir.Leib.eGP m j)
      (GlobalTheory.BZMir.Leib.hgpIncl k m j u) true (Fin.castSucc i) (Fin.castSucc i')
    have hne : GlobalTheory.BZMir.Leib.eGP m j ⟨true, Fin.castSucc i'⟩ ≠ Fin.last (m + j) :=
      fun hl => Fin.castSucc_ne_last i' ((GlobalTheory.BZMir.Leib.blockIndex_true_eq_last_iff m j _).mp hl)
    refine h.trans ((key _ _ hne).trans ?_)
    simp only [Matrix.one_apply, e_inj.eq_iff, Sigma.mk.inj_iff, heq_eq_eq, true_and,
      Fin.castSucc_inj, Units.val_one]

end GlobalTheory.CompanionTheory.GpUnip
end
end

section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib

namespace GlobalTheory.CompanionTheory.GPMem

theorem mem_mirabolicParabolic_iff_mirabolicProj_mem_parabolic (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (m j : ℕ) (g : Mir k (m + j)) :
    g ∈ MirabolicParabolic k m j ↔ mirabolicProjection k (m + j) g ∈ parab k (two (stdSum (rfl : m + j = m + j))) := by
  have hlast : ((g : GL (Fin (m + j + 1)) k) : Matrix (Fin (m + j + 1)) (Fin (m + j + 1)) k)
      (Fin.last (m + j)) = GlobalTheory.BZMir.eLast k (m + j) :=
    (GlobalTheory.BZMir.mem_Mir_iff k (g : GL (Fin (m + j + 1)) k)).1 g.2
  have hproj : ∀ a b : Fin (m + j),
      ((GlobalTheory.BZMir.mirabolicProjection k (m + j) g : GL (Fin (m + j)) k) : Matrix (Fin (m + j)) (Fin (m + j)) k) a b =
        ((g : GL (Fin (m + j + 1)) k) : Matrix (Fin (m + j + 1)) (Fin (m + j + 1)) k)
          (Fin.castSucc a) (Fin.castSucc b) := fun _ _ => rfl
  simp only [GlobalTheory.BZMir.Leib.MirabolicParabolic, GlobalTheory.BZMir.Leib.eGP, Subgroup.mem_comap,
    Subgroup.coe_subtype, GlobalTheory.SmGL.mem_parab_two, hproj]
  constructor
  · intro h b a
    convert h (Fin.castSucc b) a using 2 <;> apply Fin.ext <;>
      simp [GlobalTheory.SmGL.stdSum_inl, GlobalTheory.SmGL.stdSum_inr]
  · intro h b a
    induction b using Fin.lastCases with
    | last =>
      have h0 : ((g : GL (Fin (m + j + 1)) k) : Matrix (Fin (m + j + 1)) (Fin (m + j + 1)) k)
          (Fin.last (m + j))
          (Fin.castSucc (GlobalTheory.SmGL.stdSum (rfl : m + j = m + j) (Sum.inl a))) = 0 := by
        rw [hlast]
        simp only [GlobalTheory.BZMir.eLast, Pi.single_apply]
        rw [if_neg (Fin.castSucc_lt_last _).ne]
      convert h0 using 2 <;> apply Fin.ext <;>
        simp [GlobalTheory.SmGL.stdSum_inl, GlobalTheory.SmGL.stdSum_inr]
    | cast b =>
      convert h b a using 2 <;> apply Fin.ext <;>
        simp [GlobalTheory.SmGL.stdSum_inl, GlobalTheory.SmGL.stdSum_inr]

end GlobalTheory.CompanionTheory.GPMem
end

section

open Finset Matrix PositivityTheory.RgHe.Frame


theorem _root_.GlobalTheory.T.exists_unitary_interlacing_realization : ∀ (n : ℕ) (ε : Fin (n + 1) → Bool) (d : Fin (n + 1) → ℝ) (ε' : Fin n → Bool) (d' : Fin n → ℝ) (e : Fin n ⊕ Unit ≃ Fin (n + 1)), ε (e (Sum.inr ())) = true → (∀ a, ε (e (Sum.inl a)) = ε' a) → Function.Injective (Sum.elim d d') → (∀ i, 0 < (if ε i then (1 : ℝ) else -1) * pfD d d' i) → (∀ j, 0 < -((if ε' j then (1 : ℝ) else -1) * pfR d d' j)) → ∃ g X : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ, Formalism.REAL.inUJ ε g ∧ X * g = g * diagonal (fun i => ((d i : ℝ) : ℂ)) ∧ (∀ a b, X (e (Sum.inl a)) (e (Sum.inl b)) = if a = b then ((d' a : ℝ) : ℂ) else 0) ∧ ∀ i, ((Formalism.REAL.Jm ε * gᴴ * Formalism.REAL.Jm ε) *ᵥ (Pi.single (e (Sum.inr ())) (1 : ℂ) : Fin (n + 1) → ℂ)) i ≠ 0 := by
  first | exact @GlobalTheory.CompanionTheory.RgHeFrame.build | exact GlobalTheory.CompanionTheory.RgHeFrame.build | (intros; apply GlobalTheory.CompanionTheory.RgHeFrame.build <;> assumption)
end
