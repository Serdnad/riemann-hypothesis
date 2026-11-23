module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle101
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle003
public import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle003
public import Formalism.HermitianLattices.HermitianLatticesProofs.IsomAct
public import Formalism.SharpRestriction.CuspSpanNormBounds.IsTermOver
public import Formalism.LocalRingCardinality.DataHost
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AtBase
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle018
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle017
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NGAnalytic
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.StepHeightOfNormOne
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RowsConc
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.PoincareConstantEq
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.HidaSetting
import Formalism.SharpRestriction.CuspSpanNormBounds.IsPrimitiveSub
import Formalism.SharpRestriction.CuspSpanNormBounds.LocalGroupInFamilyNontrivial
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001

@[expose] public section

section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.FourierDecayAlt Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.SnFam
open scoped Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.DcosetCompl

section Gen

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : Formalism.BasicNotions.HSpace E}

theorem mem_orth_iff (U : Submodule E S.V) (v : S.V) : v ∈ orth S U ↔ ∀ y ∈ U, S.hT y v = 0 := by
  simp [orth, Submodule.mem_iInf, LinearMap.mem_ker]

theorem orth_anti {U U' : Submodule E S.V} (h : U ≤ U') : orth S U' ≤ orth S U := by
  intro v hv
  rw [mem_orth_iff] at hv ⊢
  exact fun y hy => hv y (h hy)

theorem le_spanE_inf (Λ : Submodule (𝓞 E) S.V) (hΛ : Submodule.IsFullLattice E Λ) (U : Submodule E S.V) :
    U ≤ spanE S (Λ ⊓ toO S U) := by
  exact _root_.GlobalTheory.SpanInfDenominators.le_spanE_inf_toO Λ hΛ U

end Gen

end GlobalTheory.DcosetCompl

namespace GlobalTheory.DcosetCompl

section Flags

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : Formalism.BasicNotions.HSpace E} {r : ℕ}

theorem xa_eq_x_of_le {T : E} (F : Formalism.MainNotions.S.FlagG S r T) {j : ℕ} (hj : r ≤ j) : F.Xa j = F.X := by
  unfold Formalism.MainNotions.S.FlagG.Xa Formalism.MainNotions.S.FlagG.X
  congr 1
  ext v
  simp only [Set.mem_image, Set.mem_setOf_eq, Set.mem_range]
  constructor
  · rintro ⟨i, _, rfl⟩; exact ⟨i, rfl⟩
  · rintro ⟨i, rfl⟩; exact ⟨i, lt_of_lt_of_le i.2 hj, rfl⟩

theorem z_mem_orth {T : E} (F : Formalism.MainNotions.S.FlagG S r T) : F.z ∈ orth S F.X := by
  rw [mem_orth_iff]
  intro y hy
  have : F.X ≤ LinearMap.ker (S.hT.flip F.z) := by
    unfold Formalism.MainNotions.S.FlagG.X
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    simp [F.z_orth i]
  simpa using this hy

theorem map_eq_of_sub_mem (g : S.V ≃ₗ[E] S.V) (X : Submodule E S.V) (h : ∀ x ∈ X, g x - x ∈ X) :
    X.map (g : S.V →ₗ[E] S.V) = X := by
  have hle : X.map (g : S.V →ₗ[E] S.V) ≤ X := by
    rintro _ ⟨x, hx, rfl⟩
    have := X.add_mem (h x hx) hx
    simpa using this
  exact Submodule.eq_of_le_of_finrank_eq hle (LinearEquiv.finrank_map_eq g X)

end Flags

end GlobalTheory.DcosetCompl

namespace GlobalTheory.DcosetCompl

section Main

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : Formalism.BasicNotions.HSpace E} {r : ℕ}

theorem sub_le_uue {T T' : E} (Λ : Submodule (𝓞 E) S.V) (hΛ : Submodule.IsFullLattice E Λ)
    (F : LFlag S r T) (F' : LFlag S r T') :
    Xsp F ≤ UUE Λ F F' ∧ Xsp F' ≤ UUE Λ F F' ∧ F.zt ∈ UUE Λ F F' ∧ F'.zt ∈ UUE Λ F F' := by
  have hUU : UU Λ F F' = XLam Λ F ⊔ Submodule.span (𝓞 E) {F.zt} ⊔ XLam Λ F' ⊔ Submodule.span (𝓞 E) {F'.zt} := rfl
  have h1 : XLam Λ F ≤ UU Λ F F' := by
    rw [hUU]; exact le_sup_left.trans (le_sup_left.trans le_sup_left)
  have h2 : XLam Λ F' ≤ UU Λ F F' := by
    rw [hUU]; exact le_sup_right.trans le_sup_left
  have h3 : F.zt ∈ UU Λ F F' := by
    rw [hUU]
    exact Submodule.mem_sup_left (Submodule.mem_sup_left (Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)))
  have h4 : F'.zt ∈ UU Λ F F' := by
    rw [hUU]
    exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)
  have hs1 : spanE S (XLam Λ F) ≤ UUE Λ F F' := Submodule.span_mono (fun x hx => h1 hx)
  have hs2 : spanE S (XLam Λ F') ≤ UUE Λ F F' := Submodule.span_mono (fun x hx => h2 hx)
  have hl1 : Xsp F ≤ spanE S (XLam Λ F) := le_spanE_inf Λ hΛ _
  have hl2 : Xsp F' ≤ spanE S (XLam Λ F') := le_spanE_inf Λ hΛ _
  exact ⟨hl1.trans hs1, hl2.trans hs2, Submodule.subset_span h3, Submodule.subset_span h4⟩

theorem uue_le {T T' : E} (Λ : Submodule (𝓞 E) S.V) (F : LFlag S r T) (F'' : LFlag S r T')
    (hz : F.zt = F.fl.z) (hz'' : F''.zt = F''.fl.z) (M : Submodule E S.V)
    (hX : Xsp F ≤ M) (hX'' : Xsp F'' ≤ M) (hzM : F.fl.z ∈ M) (hz''M : F''.fl.z ∈ M) :
    UUE Λ F F'' ≤ M := by
  unfold UUE spanE
  rw [Submodule.span_le]
  have : UU Λ F F'' ≤ M.restrictScalars (𝓞 E) := by
    refine sup_le (sup_le (sup_le ?_ ?_) ?_) ?_
    · exact fun x hx => hX hx.2
    · exact Submodule.span_le.mpr (Set.singleton_subset_iff.mpr (by rw [hz]; exact hzM))
    · exact fun x hx => hX'' hx.2
    · exact Submodule.span_le.mpr (Set.singleton_subset_iff.mpr (by rw [hz'']; exact hz''M))
  exact fun v hv => this hv

theorem th_eq_hp_gen {T T' : E} (Λ : Submodule (𝓞 E) S.V) (hΛ : Submodule.IsFullLattice E Λ)
    (F : LFlag S r T) (F' F'' : LFlag S r T')
    (hz : F.zt = F.fl.z) (hz' : F'.zt = F'.fl.z) (hz'' : F''.zt = F''.fl.z)
    (n m : S.V ≃ₗ[E] S.V) (hni : ∀ x y, S.hT (n x) (n y) = S.hT x y)
    (hnX : ∀ x ∈ Xsp F, n x - x ∈ Xsp F) (hnP : ∀ x ∈ orth S (Xsp F), n x - x ∈ Xsp F)
    (hmX : ∀ x ∈ Xsp F', m x - x ∈ Xsp F') (hmP : ∀ x ∈ orth S (Xsp F'), m x - x ∈ Xsp F')
    (hfr : ∀ a, frame F'' a = (n * m) (frame F' a)) :
    Th Λ F F' F'' (n * m) = Hp Λ F F' := by
  obtain ⟨hXU, hX'U, hzU, hz'U⟩ := sub_le_uue Λ hΛ F F'
  rw [hz] at hzU; rw [hz'] at hz'U
  have hcomp : ((n * m : S.V ≃ₗ[E] S.V) : S.V →ₗ[E] S.V) = (n : S.V →ₗ[E] S.V).comp (m : S.V →ₗ[E] S.V) := by
    ext x; rfl
  have he : ∀ i, F''.fl.e i = n (m (F'.fl.e i)) := by
    intro i
    have := hfr (Fin.castSucc i)
    simpa [frame, Formalism.MainNotions.S.FlagG.fvec, Fin.snoc_castSucc] using this
  have hzz : F''.fl.z = n (m F'.fl.z) := by
    have := hfr (Fin.last r)
    simpa [frame, Formalism.MainNotions.S.FlagG.fvec, Fin.snoc_last] using this
  have hmX' : (Xsp F').map (m : S.V →ₗ[E] S.V) = Xsp F' := map_eq_of_sub_mem m _ hmX
  have hnXF : (Xsp F).map (n : S.V →ₗ[E] S.V) = Xsp F := map_eq_of_sub_mem n _ hnX
  have hX'' : Xsp F'' = (Xsp F').map (n : S.V →ₗ[E] S.V) := by
    have h0 : Xsp F'' = (Xsp F').map ((n * m : S.V ≃ₗ[E] S.V) : S.V →ₗ[E] S.V) := by
      show F''.fl.X = F'.fl.X.map _
      unfold Formalism.MainNotions.S.FlagG.X
      rw [Submodule.map_span, ← Set.range_comp]
      have hfun : F''.fl.e = (((n * m : S.V ≃ₗ[E] S.V) : S.V →ₗ[E] S.V) ∘ F'.fl.e) := funext fun i => he i
      rw [hfun]
    rw [h0, hcomp, Submodule.map_comp, hmX']
  have hUle : UUE Λ F F'' ≤ (UUE Λ F F').map (n : S.V →ₗ[E] S.V) := by
    refine uue_le Λ F F'' hz hz'' _ ?_ ?_ ?_ ?_
    · rw [← hnXF]; exact Submodule.map_mono hXU
    · rw [hX'']; exact Submodule.map_mono hX'U
    · have h1 : n F.fl.z ∈ (UUE Λ F F').map (n : S.V →ₗ[E] S.V) := Submodule.mem_map_of_mem hzU
      have h2 : n F.fl.z - F.fl.z ∈ (UUE Λ F F').map (n : S.V →ₗ[E] S.V) := by
        have h3 := hnP _ (z_mem_orth F.fl)
        rw [← hnXF] at h3
        exact Submodule.map_mono hXU h3
      have := Submodule.sub_mem _ h1 h2
      simpa using this
    · rw [hzz]
      apply Submodule.mem_map_of_mem
      have hm1 : m F'.fl.z - F'.fl.z ∈ UUE Λ F F' := hX'U (hmP _ (z_mem_orth F'.fl))
      have := Submodule.add_mem _ hm1 hz'U
      simpa using this
  apply le_antisymm
  · rw [Th, Submodule.map_le_iff_le_comap]
    rintro ⟨a, b⟩ hp
    exact hp.1.1.1
  · intro x hx
    have hxP : x ∈ orth S (Xsp F) := orth_anti hXU hx
    have hxP' : x ∈ orth S (Xsp F') := orth_anti hX'U hx
    refine ⟨(x, n x), ⟨⟨⟨hx, ?_⟩, ?_⟩, ?_⟩, rfl⟩
    · show n x ∈ orth S (UUE Λ F F'')
      rw [mem_orth_iff]
      intro w hw
      obtain ⟨w0, hw0, rfl⟩ := hUle hw
      show S.hT (n w0) (n x) = 0
      rw [hni]
      exact (mem_orth_iff _ _).1 hx w0 hw0
    · show x - n x ∈ Xsp F
      have := neg_mem (hnP x hxP)
      simpa using this
    · show n (m x) - n x ∈ Xsp F''
      rw [hX'']
      refine ⟨m x - x, hmP x hxP', ?_⟩
      simp [map_sub]

end Main

end GlobalTheory.DcosetCompl

namespace GlobalTheory.DcosetCompl

theorem th_eq_hp : ∀ (D : D7) {T T' : D.host.E} (Λ : Submodule (𝓞 D.host.E) (VS D).V) (F : LFlag (D.sp.Y 0) D.R.rS T) (F' F'' : LFlag (D.sp.Y 0) D.R.rS T'), Submodule.IsFullLattice D.host.E Λ → F.zt = F.fl.z → F'.zt = F'.fl.z → F''.zt = F''.fl.z → ∀ n ∈ NRat F, ∀ m ∈ NRat F', (∀ a, frame F'' a = (n * m) (frame F' a)) → Th Λ F F' F'' (n * m) = Hp Λ F F' := by
  intro D T T' Λ F F' F'' hΛ hz hz' hz'' n hn m hm hfr
  have hnX : ∀ x ∈ Xsp F, n x - x ∈ Xsp F := by
    intro x hx
    have h := hn.2.1 D.R.rS x (by
      show x ∈ F.fl.Xa (D.R.rS + 1)
      rw [xa_eq_x_of_le F.fl (Nat.le_succ _)]; exact hx)
    change n x - x ∈ F.fl.Xa D.R.rS at h
    rwa [xa_eq_x_of_le F.fl (le_refl _)] at h
  have hmX : ∀ x ∈ Xsp F', m x - x ∈ Xsp F' := by
    intro x hx
    have h := hm.2.1 D.R.rS x (by
      show x ∈ F'.fl.Xa (D.R.rS + 1)
      rw [xa_eq_x_of_le F'.fl (Nat.le_succ _)]; exact hx)
    change m x - x ∈ F'.fl.Xa D.R.rS at h
    rwa [xa_eq_x_of_le F'.fl (le_refl _)] at h
  exact th_eq_hp_gen Λ hΛ F F' F'' hz hz' hz'' n m (fun x y => hn.1 x y) hnX hn.2.2 hmX hm.2.2 hfr

end GlobalTheory.DcosetCompl
end
end

section

open NumberField MeasureTheory Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.TermLoc Formalism.L2.SG.RowsConc Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.FourierDecayAlt GlobalTheory.Unfold GlobalTheory.LocOver GlobalTheory.GenMass
open scoped Classical ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.GlueStable

theorem glueSet_gmap_mem : ∀ (D : D7) (U : Submodule D.host.E (VS D).V) (M : Submodule (𝓞 D.host.E) (VS D).V), ∀ g ∈ Formalism.L2.SG.Pf.Cnt.isomFix (VS D).hT U, ∀ Λ ∈ Formalism.L2.SG.Pf.Cnt.GlueSet (VS D).hT U M, Formalism.HermitianLatticesTheory.gmap g Λ ∈ Formalism.L2.SG.Pf.Cnt.GlueSet (VS D).hT U M := by
  intro D U M g hg Λ hΛ
  obtain ⟨hgI, hgU⟩ := hg
  obtain ⟨hlat, huni, hcap⟩ := hΛ
  have H := Formalism.HermitianLatticesTheory.isomAct _ _ _ (VS D).hT g hgI Λ
  refine ⟨H.2.2.2.2.mpr hlat, H.2.2.2.1.mpr huni, ?_⟩
  rw [← hcap]
  ext x
  simp only [Submodule.mem_inf, Submodule.restrictScalars_mem, Formalism.HermitianLatticesTheory.isomAct_mem_gmap]
  constructor
  · rintro ⟨h1, h2⟩
    have e : g.symm x = x := by
      conv_lhs => rw [← hgU x h2]
      simp
    exact ⟨e ▸ h1, h2⟩
  · rintro ⟨h1, h2⟩
    have e : g.symm x = x := by
      conv_lhs => rw [← hgU x h2]
      simp
    exact ⟨e.symm ▸ h1, h2⟩

end GlobalTheory.GlueStable
end

section

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc GlobalTheory.Unfold GlobalTheory.LocOver GlobalTheory.GenMass
open scoped Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG

namespace GlobalTheory.LocStdInt

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E]
  [TopologicalSpace E] [MeasurableSpace E] {M : Model F E} {V : Type} [AddCommGroup V] [Module E V]

lemma cj_mem {x : E} (hx : x ∈ M.L.O) : M.L.cj x ∈ M.L.O := by
  rw [M.L.O_def] at hx ⊢
  exact hx.map (M.L.cj.toAlgHom.restrictScalars (Valuation.integer (ValuativeRel.valuation F)))

def hl (H : HermSp M V) (y : V) : V →ₗ[E] E where
  toFun x := H.h x y
  map_add' x x' := H.h_add_left x x' y
  map_smul' a x := H.h_smul_left a x y

lemma h_prF (H : HermSp M V) {r : ℕ} (Fr : FrameD H r) (v y : V) :
    H.h (Fr.prF v) y = H.h v y - ∑ a, H.h v (Fr.es a) * H.h (Fr.e a) y
      - ∑ a, H.h v (Fr.e a) * H.h (Fr.es a) y := by
  show hl H y (Fr.prF v) = _

  simp only [FrameD.prF, map_sub, map_sum, map_smul, smul_eq_mul]
  rfl

lemma h_expand (H : HermSp M V) {r : ℕ} (Fr : FrameD H r) (v y : V) :
    H.h v y = H.h (Fr.prF v) y + ∑ a, H.h v (Fr.es a) * H.h (Fr.e a) y
      + ∑ a, H.h v (Fr.e a) * H.h (Fr.es a) y := by
  rw [h_prF H Fr v y]
  ring

lemma h_prF_es (H : HermSp M V) {r : ℕ} (Fr : FrameD H r) (v : V) (b : Fin r) :
    H.h (Fr.prF v) (Fr.es b) = 0 := by
  rw [h_prF H Fr v (Fr.es b)]
  have hdual : ∀ a, H.h (Fr.e a) (Fr.es b) = if a = b then 1 else 0 := fun a => Fr.h_es a b
  simp [hdual, Fr.h_ss]

lemma h_symm_mem (H : HermSp M V) {x y : V} (h : H.h x y ∈ M.L.O) : H.h y x ∈ M.L.O := by
  rw [H.h_herm]
  exact cj_mem h

lemma span_left (H : HermSp M V) (S : Set V) (y : V) (h : ∀ x ∈ S, H.h x y ∈ M.L.O) :
    ∀ x ∈ Submodule.span M.L.O S, H.h x y ∈ M.L.O := by
  intro x hx
  induction hx using Submodule.span_induction with
  | mem x hx => exact h x hx
  | zero =>
    have h0 : H.h 0 y = 0 := (hl H y).map_zero
    rw [h0]
    exact zero_mem _
  | add x x' _ _ hx hx' =>
    rw [H.h_add_left]
    exact add_mem hx hx'
  | smul c x _ hx =>
    rw [Subring.smul_def, H.h_smul_left]
    exact mul_mem c.2 hx

private lemma form_mem_O_of_frame_coords_mem_O (H : HermSp M V) {r : ℕ} (Fr : FrameD H r) (L : Submodule M.L.O (H.Wb Fr.f))
    (hL : Fr.IsInner L) {u v : V}
    (hu : (∀ a, H.h u (Fr.es a) ∈ M.L.O) ∧ (∀ a, H.h u (Fr.e a) ∈ M.L.O) ∧
      ∃ w : ↥(H.perp (H.X Fr.f)), (w : V) = Fr.prF u ∧ H.mkW Fr.f w ∈ L)
    (hv : (∀ a, H.h v (Fr.es a) ∈ M.L.O) ∧ (∀ a, H.h v (Fr.e a) ∈ M.L.O) ∧
      ∃ w : ↥(H.perp (H.X Fr.f)), (w : V) = Fr.prF v ∧ H.mkW Fr.f w ∈ L) :
    H.h u v ∈ M.L.O := by
  obtain ⟨hus, hue, wu, hwu, hwuL⟩ := hu
  obtain ⟨hvs, hve, wv, hwv, hwvL⟩ := hv
  have hpp : H.h (Fr.prF v) (Fr.prF u) ∈ M.L.O := by
    have h0 := (hL.2.1 wv).1 hwvL wu hwuL
    rwa [hwv, hwu] at h0
  have hwu0 : ∀ x ∈ H.X Fr.f, H.h (wu : V) x = 0 := wu.2
  have he0 : ∀ a, H.h (Fr.e a) (Fr.prF u) = 0 := by
    intro a
    rw [H.h_herm, ← hwu, hwu0 (Fr.e a) (Submodule.subset_span ⟨a, rfl⟩), map_zero]
  have hs0 : ∀ a, H.h (Fr.es a) (Fr.prF u) = 0 := by
    intro a
    rw [H.h_herm, h_prF_es H Fr u a, map_zero]
  have hvu : H.h v (Fr.prF u) ∈ M.L.O := by
    rw [h_expand H Fr v (Fr.prF u)]
    simp only [he0, hs0, mul_zero, Finset.sum_const_zero, add_zero]
    exact hpp
  rw [h_expand H Fr u v]
  refine add_mem (add_mem (h_symm_mem H hvu) ?_) ?_
  · exact sum_mem fun a _ => mul_mem (hus a) (h_symm_mem H (hve a))
  · exact sum_mem fun a _ => mul_mem (hue a) (h_symm_mem H (hvs a))

theorem lamStd_integral : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) {r : ℕ} (Fr : FrameD H r) (L : Submodule M.L.O (H.Wb Fr.f)) (hL : Fr.IsInner L), ∀ x ∈ Fr.LamStd L, ∀ y ∈ Fr.LamStd L, H.h x y ∈ M.L.O := by
  intro F _ _ _ E _ _ _ _ M V _ _ H r Fr L hL x hx y hy
  unfold FrameD.LamStd at hx hy
  refine span_left H _ y ?_ x hx
  intro u hu
  exact h_symm_mem H (span_left H _ u (fun v hv => form_mem_O_of_frame_coords_mem_O H Fr L hL hv hu) y hy)

end GlobalTheory.LocStdInt
end

section

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc GlobalTheory.Unfold GlobalTheory.LocOver GlobalTheory.GenMass
open scoped Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG

namespace GlobalTheory

theorem satur_of_gram_det_unit : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) {ι : Type} [Fintype ι] [DecidableEq ι] (Λ : Submodule M.L.O V) (hΛ : ∀ x ∈ Λ, ∀ y ∈ Λ, H.h x y ∈ M.L.O) (m : ι → V) (hm : ∀ i, m i ∈ Λ) (hdet : IsUnitO M (H.gram m).det), ∀ v ∈ Λ, v ∈ Submodule.span E (Set.range m) → v ∈ Submodule.span M.L.O (Set.range m) := by
  intro F _ _ _ E _ _ _ _ M V _ _ H ι _ _ Λ hΛ m hm hdet v hv hvE
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun E).1 hvE

  have hG : ∀ a b, H.gram m a b ∈ M.L.O := fun a b => hΛ _ (hm b) _ (hm a)
  let G' : Matrix ι ι M.L.O := Matrix.of fun a b => ⟨H.gram m a b, hG a b⟩
  have hmap : M.L.O.subtype.mapMatrix G' = H.gram m := by
    ext a b
    rfl
  have hadj : ∀ a b, (H.gram m).adjugate a b ∈ M.L.O := by
    intro a b
    rw [← hmap, ← RingHom.map_adjugate]
    exact (G'.adjugate a b).2

  have hpair : ∀ a, (Matrix.mulVec (H.gram m) c) a ∈ M.L.O := by
    intro a
    have hsum : H.h (∑ i, c i • m i) (m a) = (Matrix.mulVec (H.gram m) c) a := by
      let φ : V →+ E := AddMonoidHom.mk' (fun x => H.h x (m a)) (fun x x' => H.h_add_left x x' (m a))
      have hφ : H.h (∑ i, c i • m i) (m a) = φ (∑ i, c i • m i) := rfl

      rw [hφ, map_sum]
      simp only [Matrix.mulVec, dotProduct, HermSp.gram, Matrix.of_apply]
      refine Finset.sum_congr rfl fun i _ => ?_
      show H.h (c i • m i) (m a) = _
      rw [H.h_smul_left, mul_comm]
    rw [← hsum]
    exact hΛ _ hv _ (hm a)

  have hdc : ∀ i, (H.gram m).det * c i ∈ M.L.O := by
    intro i
    have key : Matrix.mulVec (H.gram m).adjugate (Matrix.mulVec (H.gram m) c) = (H.gram m).det • c := by
      rw [Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec]
    have hi := congrFun key i
    rw [Pi.smul_apply, smul_eq_mul] at hi
    have hmem : ∀ w : ι → E, (∀ j, w j ∈ M.L.O) → (Matrix.mulVec (H.gram m).adjugate w) i ∈ M.L.O := by
      intro w hw
      simp only [Matrix.mulVec, dotProduct]
      exact Subring.sum_mem _ fun j _ => Subring.mul_mem _ (hadj i j) (hw j)
    rw [← hi]
    exact hmem _ hpair

  obtain ⟨_, y, hy, hdy⟩ := hdet
  have hc : ∀ i, c i ∈ M.L.O := by
    intro i
    have hci : c i = y * ((H.gram m).det * c i) := by
      rw [← mul_assoc, mul_comm y, hdy, one_mul]
    rw [hci]
    exact Subring.mul_mem _ hy (hdc i)
  refine Submodule.sum_mem _ fun i _ => ?_
  have hsm : c i • m i = (⟨c i, hc i⟩ : M.L.O) • m i := rfl
  rw [hsm]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

end GlobalTheory
end

end

section

@[expose] public section

open NumberField MeasureTheory Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.TermLoc Formalism.L2.SG.RowsConc Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.FourierDecayAlt GlobalTheory.Unfold GlobalTheory.LocOver GlobalTheory.GenMass
open scoped Classical ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.isometryFixingSpan_preserves_gluedLattices : ∀ (D : D7) (U : Submodule D.host.E (VS D).V) (M : Submodule (𝓞 D.host.E) (VS D).V), ∀ g ∈ Formalism.L2.SG.Pf.Cnt.isomFix (VS D).hT U, ∀ Λ ∈ Formalism.L2.SG.Pf.Cnt.GlueSet (VS D).hT U M, Formalism.HermitianLatticesTheory.gmap g Λ ∈ Formalism.L2.SG.Pf.Cnt.GlueSet (VS D).hT U M := by
  first | exact @GlobalTheory.GlueStable.glueSet_gmap_mem | exact GlobalTheory.GlueStable.glueSet_gmap_mem | (intros; apply GlobalTheory.GlueStable.glueSet_gmap_mem <;> assumption)

end
end

section

@[expose] public section

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc GlobalTheory.Unfold GlobalTheory.LocOver GlobalTheory.GenMass
open scoped Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG

theorem _root_.GlobalTheory.T.frameStandardLattice_hermitian_integral : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) {r : ℕ} (Fr : FrameD H r) (L : Submodule M.L.O (H.Wb Fr.f)) (hL : Fr.IsInner L), ∀ x ∈ Fr.LamStd L, ∀ y ∈ Fr.LamStd L, H.h x y ∈ M.L.O := by
  first | exact @GlobalTheory.LocStdInt.lamStd_integral | exact GlobalTheory.LocStdInt.lamStd_integral | (intros; apply GlobalTheory.LocStdInt.lamStd_integral <;> assumption)

end
end

section

@[expose] public section

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc GlobalTheory.Unfold GlobalTheory.LocOver GlobalTheory.GenMass
open scoped Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG

theorem _root_.GlobalTheory.T.saturated_span_of_gramDet_isUnit_integralLattice : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) {ι : Type} [Fintype ι] [DecidableEq ι] (Λ : Submodule M.L.O V) (hΛ : ∀ x ∈ Λ, ∀ y ∈ Λ, H.h x y ∈ M.L.O) (m : ι → V) (hm : ∀ i, m i ∈ Λ) (hdet : IsUnitO M (H.gram m).det), ∀ v ∈ Λ, v ∈ Submodule.span E (Set.range m) → v ∈ Submodule.span M.L.O (Set.range m) := by
  first | exact @GlobalTheory.satur_of_gram_det_unit | exact GlobalTheory.satur_of_gram_det_unit | (intros; apply GlobalTheory.satur_of_gram_det_unit <;> assumption)

end
end
