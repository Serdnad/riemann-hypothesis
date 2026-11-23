module

import Formalism.LocalToGlobal.IndefiniteReal.SchurOrthogonality
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.Bundle007
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.Bundle003
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.UnimodInst
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.Bundle008
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.Bundle009
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasWeil
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle020
import Formalism.LocalToGlobal.IndefiniteReal.Bundle014
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

@[expose] public section

section

noncomputable section

open MeasureTheory
open scoped TensorProduct

namespace Formalism.IndefR.Eqv

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Sobolev₂

variable {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {Lie : Set (Matrix (Fin n) (Fin n) ℂ)} {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

theorem sobCont_zero : Sobolev₂ Lie σ 0 :=
  ⟨[], 0, by simp, fun w _ => by simp⟩

theorem sobCont_add {ℓ₁ ℓ₂ : H →ₗ[ℂ] ℂ} (h₁ : Sobolev₂ Lie σ ℓ₁) (h₂ : Sobolev₂ Lie σ ℓ₂) :
    Sobolev₂ Lie σ (ℓ₁ + ℓ₂) := by
  apply Formalism.IndefR.SchurOrthogonalityAlt.sobCont_add <;> assumption

theorem sobCont_smul {ℓ : H →ₗ[ℂ] ℂ} (c : ℂ) (h : Sobolev₂ Lie σ ℓ) : Sobolev₂ Lie σ (c • ℓ) := by
  obtain ⟨S, C, hS, hb⟩ := h
  refine ⟨S, ‖c‖ * C, hS, fun w hw => ?_⟩
  rw [LinearMap.smul_apply, norm_smul, mul_assoc]
  exact mul_le_mul_of_nonneg_left (hb w hw) (norm_nonneg c)

end Sobolev₂

variable {D : D7}


open Classical in
def ContAt {V : HSp D} {S : D.what₂.Tau → SPar} (M : Mult.DSModel V S) (T : Mult.MMap M) : Prop :=
  ∀ τ (v : M.Vec) (x : GA D V), ∃ ℓ : M.H τ →ₗ[ℂ] ℂ, Sobolev₂ (lieAt V τ) (M.rep τ) ℓ ∧
    ∀ w : M.sm τ, ℓ w = T (Function.update v τ w) x

open Classical in
theorem contAt_of_mem {V : HSp D} {S : D.what₂.Tau → SPar} {M : Mult.DSModel V S}
    {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} {J : Set (GA D V)} {χ : GA D V → ℂ}
    {T : Mult.MMap M} (hT : T ∈ Mult.Mult θ M J χ) : ContAt M T := by
  induction hT using Submodule.span_induction with
  | mem T hT => exact hT.cont
  | zero =>
    intro τ v x
    exact ⟨0, sobCont_zero, fun w => by simp⟩
  | add T₁ T₂ _ _ h₁ h₂ =>
    intro τ v x
    obtain ⟨ℓ₁, hc₁, he₁⟩ := h₁ τ v x
    obtain ⟨ℓ₂, hc₂, he₂⟩ := h₂ τ v x
    exact ⟨ℓ₁ + ℓ₂, sobCont_add hc₁ hc₂, fun w => by simp [he₁, he₂]⟩
  | smul c T _ h =>
    intro τ v x
    obtain ⟨ℓ, hc, he⟩ := h τ v x
    exact ⟨c • ℓ, sobCont_smul c hc, fun w => by simp [he]⟩

open Classical in
theorem ioUniqueAt_holds (D : D7) : IoUniqueAt D := by
  intro V S M θ J χ Kf Sinf Ds _ _ _ _ T hdense hspan u hu hvan
  rw [Mult.mem_multT] at hu
  have hcont : ContAt M (PiTensorProduct.lift.symm u) := contAt_of_mem hu
  have hsub : Submodule.span ℂ {x | ∃ φ w, T φ w = x} ≤ LinearMap.ker u := by
    rw [Submodule.span_le]
    rintro x ⟨φ, w, rfl⟩
    exact hvan φ w
  have hvK : ∀ v : ∀ τ, M.sm τ, (∀ τ, v τ ∈ Kf τ) → u (PiTensorProduct.tprod ℂ v) = 0 :=
    fun v hv => hsub (hspan v hv)
  have hTe : ∀ v, PiTensorProduct.lift.symm u v = u (PiTensorProduct.tprod ℂ v) := fun v => by simp
  have main : ∀ s : Finset D.what₂.Tau, ∀ v : ∀ τ, M.sm τ, (∀ τ ∉ s, v τ ∈ Kf τ) →
      PiTensorProduct.lift.symm u v = 0 := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro v hv
      rw [hTe]
      exact hvK v fun τ => hv τ (Finset.notMem_empty τ)
    | insert τ s hτ ih =>
      intro v hv
      funext x
      obtain ⟨ℓ, hℓ, hℓv⟩ := hcont τ v x
      have h0 : ∀ w ∈ Kf τ, ℓ (w : M.H τ) = 0 := by
        intro w hw
        rw [hℓv w, ih (Function.update v τ w) ?_, Pi.zero_apply]
        intro ρ hρ
        by_cases h : ρ = τ
        · subst h
          simpa using hw
        · rw [Function.update_of_ne h]
          exact hv ρ (by simp [Finset.mem_insert, h, hρ])
      have h1 := hdense τ ℓ hℓ h0 (v τ)
      rw [hℓv (v τ), Function.update_eq_self] at h1
      exact h1
  have hall : ∀ v, u (PiTensorProduct.tprod ℂ v) = 0 := fun v => by
    rw [← hTe]
    exact main Finset.univ v fun τ h => absurd (Finset.mem_univ τ) h
  apply PiTensorProduct.ext
  ext v
  simp [hall]

end Formalism.IndefR.Eqv

end
end

section

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open scoped TensorProduct Matrix

namespace Formalism.IndefR.Eqv

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {V : HSp D} (fr : UI.Frames D V)

def kf (K : Subgroup (GL (Fin V.rank) (Lev.EAf D))) : Set (UI.instV fr).Gf :=
  {y | (y.1 : GL (Fin V.rank) (Lev.EAf D)) ∈ K}

theorem brg_mem_levA (K : Subgroup (GL (Fin V.rank) (Lev.EAf D))) (x : (UI.instV fr).GA) :
    UI.brg fr x ∈ Lev.levA V K ↔ x.1 = 1 ∧ x.2 ∈ kf fr K := by
  show UI.brg fr x ∈ GfC V ⊓ K.comap (Lev.finE V) ↔ _
  rw [Subgroup.mem_inf, Subgroup.mem_comap, brg_mem_GfC, finE_brg]
  rfl

theorem kf_isCompact_isOpen_of_levelA (K : Subgroup (GL (Fin V.rank) (Lev.EAf D))) (hK : IsLevelA V K) :
    IsCompact (kf fr K) ∧ IsOpen (kf fr K) := by
  have hpre : kf fr K = jf fr ⁻¹' (Lev.levA V K : Set (GA D V)) := by
    ext y
    show y ∈ kf fr K ↔ UI.brg fr (1, y) ∈ Lev.levA V K
    rw [brg_mem_levA]
    exact ⟨fun h => ⟨rfl, h⟩, fun h => h.2⟩
  refine ⟨?_, ?_⟩
  · rw [hpre]
    exact (jf_isClosedEmbedding fr).isCompact_preimage hK.1
  · have hmem : ∀ y, jf fr y ∈ GfC V := fun y => (brg_mem_GfC fr (1, y)).mpr rfl
    let jc : (UI.instV fr).Gf → GfC V := fun y => ⟨jf fr y, hmem y⟩
    have hjc : Continuous jc := (jf_isClosedEmbedding fr).continuous.subtype_mk _
    have e : kf fr K = jc ⁻¹' (((Lev.levA V K).subgroupOf (GfC V)) : Set (GfC V)) := by
      rw [hpre]
      ext y
      simp only [Set.mem_preimage, SetLike.mem_coe, Subgroup.mem_subgroupOf, jc]
    rw [e]
    exact hK.2.preimage hjc


end Formalism.IndefR.Eqv

end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open scoped TensorProduct InnerProductSpace

namespace Formalism.IndefR.Eqv.Act

open Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Links.RealDat

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Lift

variable {D : D7} (V : HSp D)

theorem thetaC_inj {y y' : Ainf D.host.F ⊗[D.host.F] D.host.E} (h : ∀ τ, thetaC D τ y = thetaC D τ y') : y = y' :=
  (splitEquiv D).injective (funext h)

theorem infHom_infOnly (h : GA D V) : infHom V (infOnly D V h) = infHom V h := by
  apply Units.ext
  funext i j
  show infPart D (matA D V (infOnly D V h) i j) = infPart D (matA D V h i j)
  apply thetaC_inj
  intro τ
  have e := congrFun (congrFun (infMat_infOnly D V h τ) i) j
  rw [infMat_thetaC, infMat_thetaC] at e
  exact e

theorem exists_finLift (q : Bridge.Gf V) : ∃ κ ∈ GfC V, finHom V κ = q := by
  obtain ⟨κ0, hκ0⟩ := q.2
  refine ⟨(infOnly D V κ0)⁻¹ * κ0, ?_, ?_⟩
  · show infHom V ((infOnly D V κ0)⁻¹ * κ0) = 1
    rw [map_mul, map_inv, infHom_infOnly, inv_mul_cancel]
  · have h1 : finHom V (infOnly D V κ0) = 1 := infOnly_mem_GinfC D V κ0
    rw [map_mul, map_inv, h1, inv_one, one_mul, hκ0]

end Lift

section Ad

variable {G Γ W : Type} [Group G] [Group Γ] [NormedAddCommGroup W] [InnerProductSpace ℂ W] (ι : Γ →* G)

end Ad

section Coef

variable {D : D7} {V : HSp D} (c : CoefA V)

theorem coefExt_mul (hc : c.Is) (f : Bridge.Gf V → c.W) (h κ : GA D V) (hκ : κ ∈ GfC V) :
    c.ext f (h * κ) = c.ρ h⁻¹ (f ((finHom V).rangeRestrict h * (finHom V).rangeRestrict κ)) := by
  have e1 : (finHom V).rangeRestrict (h * κ) = (finHom V).rangeRestrict h * (finHom V).rangeRestrict κ := map_mul _ _ _
  have e2 : c.ρ (h * κ)⁻¹ = c.ρ h⁻¹ := by
    rw [_root_.mul_inv_rev, map_mul, hc.1 _ (Subgroup.inv_mem _ hκ), one_mul]
  exact congrArg₂ (fun (L : Module.End ℂ c.W) z => L (f z)) e2 e1

end Coef

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
variable {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)

end Formalism.IndefR.Eqv.Act

end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open scoped TensorProduct InnerProductSpace

namespace Formalism.IndefR.Eqv.Act

open Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Links.RealDat

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
variable {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)

theorem flag_character_eq_principal (t : T) (k : GA D (Yc D 0)) :
    levChi (Yc D 0) (R.βY 0) (R.datYt t 0 R.triv) k = levChi (Yc D 0) (R.βY 0) (flag1L (R.dat0 R.triv)) k := by
  unfold levChi
  congr 1
  have e1 : levFn (R.βY 0) (R.datYt t 0 R.triv) (finE (Yc D 0) k) =
      levFn (R.βY 0) (withP (R.datYt t 0 R.triv) (LevelP.triv (R.datYt t 0 R.triv).Pg (R.datYt t 0 R.triv).r ℂ))
        (finE (Yc D 0) k) := rfl
  rw [e1, levFn_withP]
  rw [show ext1 (LevelP.triv (R.datYt t 0 R.triv).Pg (R.datYt t 0 R.triv).r ℂ).H
      (⇑(LevelP.triv (R.datYt t 0 R.triv).Pg (R.datYt t 0 R.triv).r ℂ).chi)
      (rTup (R.βY 0) (R.datYt t 0 R.triv) (finE (Yc D 0) k)) = 1 from subgroupCharExtension_one_apply _ _, one_mul, levFn_flag1]
  unfold LevCh.datYt LevCh.dat0
  exact levFn_datY_noQ rank_lowerChainSpace_zero_le (r_le_Y 0) D.R.t 0 R.Pg (R.Q t) R.triv R.chi (R.xiR t) (fun _ => 1) Frm.B _

end Formalism.IndefR.Eqv.Act

end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
  IsDedekindDomain NumberField
open scoped TensorProduct ContDiff

namespace Formalism.IndefR.Eqv

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem actO_actO (S T : HSp D) (g g' : GA D S) (h h' : GA D T) (x : WO S T) :
    actO S T g h (actO S T g' h' x) = actO S T (g * g') (h * h') x := by
  unfold actO
  rw [mul_inv_rev, mt_mul, mt_mul]
  simp only [Matrix.mul_assoc]

theorem actO_one (S T : HSp D) (x : WO S T) : actO S T 1 1 x = x := by
  unfold actO
  rw [inv_one, mt_one, mt_one]
  simp

theorem actO_inv_actO (S T : HSp D) (g : GA D S) (h : GA D T) (x : WO S T) :
    actO S T g h (actO S T g⁻¹ h⁻¹ x) = x := by
  rw [actO_actO, mul_inv_cancel, mul_inv_cancel, actO_one]

theorem actO_actO_inv (S T : HSp D) (g : GA D S) (h : GA D T) (x : WO S T) :
    actO S T g⁻¹ h⁻¹ (actO S T g h x) = x := by
  rw [actO_actO, inv_mul_cancel, inv_mul_cancel, actO_one]

theorem symplO_actO (S T : HSp D) (g : GA D S) (h : GA D T) (x y : WO S T) :
    symplO S T (actO S T g h x) (actO S T g h y) = symplO S T x y := by
  rcases le_or_gt S.rank T.rank with hr | hr
  · obtain ⟨h1, h2⟩ := Brg.bridgeSmall S T hr
    rw [h1, h1, h2, h2, sympl_actHom]
  · obtain ⟨h1, h2⟩ := Brg.bridgeLarge' S T hr
    rw [h1, h1, h2, h2, sympl_actHom]

def pull (S T : HSp D) (g : GA D S) (h : GA D T) : Module.End ℂ (WO S T → ℂ) :=
  LinearMap.funLeft ℂ ℂ (actO S T g h)

theorem mt_GQ (V : HSp D) {γ : GA D V} (hγ : γ ∈ GQ V) :
    ∃ M : Matrix (Fin V.rank) (Fin V.rank) D.host.E, Formalism.L2.Theta.mt V γ = M.map (incA D) := by
  simp only [GQ, HFinIn, HFin, Subgroup.mem_subgroupOf] at hγ
  obtain ⟨u, -, hu⟩ := hγ
  exact ⟨u.1, (congrArg Units.val hu).symm⟩

theorem continuous_actO (S T : HSp D) (g : GA D S) (h : GA D T) : Continuous (actO S T g h) := by
  unfold actO
  exact (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const

end Formalism.IndefR.Eqv

end
end
