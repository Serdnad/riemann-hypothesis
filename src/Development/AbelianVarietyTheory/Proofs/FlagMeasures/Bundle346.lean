module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.RealObj
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle036
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermOp
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RepresentationIndependence.FrameOKMap
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.PoincareInHH
import Formalism.LocalRingCardinality.SpanPowerMembership.LocAtA
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HermitianClassFiniteness.RtUnitaryOf
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle002
public import Formalism.SharpRestriction.CuspSpanNormBounds.IsTermOver
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianDoubleCosetAmplitudeBoundLocal
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle006
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AtBase
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RowsConc
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.PoincareConstantEq
import Formalism.SharpRestriction.CuspSpanNormBounds.LocalGroupInFamilyNontrivial
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle016
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.Bundle001
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001

@[expose] public section

section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.PinScale

open Formalism.L2.SG.RealObj

theorem ptEntry_row_zero {K : Type*} [Zero K] :
    ∀ (bs : List (K × ℕ)) (a b : ℕ), a < b → b < (bs.map Prod.snd).sum →
      blkOf bs a = blkOf bs b → ∃ c, c < b ∧ ∀ j, j ≤ c → Formalism.MainNotions.S.ptEntry bs c j = 0 := by
  intro bs
  induction bs with
  | nil =>
    intro a b hab hb hbl
    simp at hb
  | cons block rest ih =>
    obtain ⟨t, s⟩ := block
    intro a b hab hb hbl
    by_cases ha : a < s
    · by_cases hbs : b < s
      · refine ⟨0, by omega, fun j hj => ?_⟩
        have hj0 : j = 0 := by omega
        subst hj0
        have hs : 0 < s := by omega
        simp only [Formalism.MainNotions.S.ptEntry]
        rw [if_pos ⟨hs, hs⟩, if_neg (by omega)]
      · exfalso
        simp [blkOf, ha, hbs] at hbl
    · have hbs : ¬ b < s := by omega
      simp only [blkOf, ha, hbs, if_false] at hbl
      have hbl' : blkOf rest (a - s) = blkOf rest (b - s) := by omega
      have hb' : b - s < (rest.map Prod.snd).sum := by simp at hb; omega
      obtain ⟨c, hc, hz⟩ := ih (a - s) (b - s) (by omega) hb' hbl'
      refine ⟨c + s, by omega, fun j hj => ?_⟩
      simp only [Formalism.MainNotions.S.ptEntry]
      rw [if_neg (by omega)]
      split_ifs with h
      · have hcs : c + s - s = c := by omega
        rw [hcs]
        exact hz _ (by omega)
      · rfl

theorem isEmpty_freeE_of_reg {D : D7} (X : HidaSetting D) (u u' : D.what₂.Word)
    (w : Point D.host.E (D.R.rS + 1)) (γ : X.B.I.Ginf) (hreg : RegX X u u' γ) (hrep : IsPtRep X u u' w γ) :
    IsEmpty (FreeE w) := by
  refine ⟨fun p => ?_⟩
  obtain ⟨⟨a, b⟩, hab, hbl⟩ := p
  have hab' : a.1 < b.1 := hab
  have hsum : (w.1.map Prod.snd).sum = D.R.rS + 1 := w.2.2
  have hb := b.2
  obtain ⟨c, hcb, hz⟩ := ptEntry_row_zero w.1 a.1 b.1 hab' (by rw [hsum]; exact b.2) hbl
  obtain ⟨v⟩ : Nonempty (InfinitePlace X.B.I.F) := inferInstance
  have hle : c + 1 ≤ D.R.rS + 1 := by omega
  apply (hreg v).1 (c + 1) (by omega) (by omega)
  unfold Formalism.L2.SG.RealObj.Dl
  rw [dif_pos hle]
  apply Matrix.det_eq_zero_of_row_eq_zero ⟨c, by omega⟩
  intro j
  simp only [Matrix.submatrix_apply]
  have hrow := congrFun (congrFun (hrep v) (Fin.castLE hle ⟨c, by omega⟩)) (Fin.castLE hle j)
  simp only [ptC, Formalism.MainNotions.S.ptMat, Matrix.map_apply, Formalism.L2.SG.RealObj.ZhatO, Fin.val_castLE] at hrow
  rw [hz j.1 (by omega), map_zero, map_zero] at hrow
  rcases mul_eq_zero.mp hrow with h | h
  · exact absurd h (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))
  · exact h

theorem ptRep_unique {D : D7} (X : HidaSetting D) (u u' : D.what₂.Word) {w w' : Point D.host.E (D.R.rS + 1)}
    {γ : X.B.I.Ginf} (h : IsPtRep X u u' w γ) (h' : IsPtRep X u u' w' γ) : w = w' := by
  obtain ⟨v⟩ : Nonempty (InfinitePlace X.B.I.F) := inferInstance
  have e := (h v).symm.trans (h' v)
  apply GlobalTheory.IntTerm.ptMat_injective
  refine Matrix.ext fun i j => ?_
  have hij := congrFun (congrFun e i) j
  simp only [ptC, Matrix.map_apply] at hij
  exact X.ιE.symm.injective ((X.B.I.φ v).injective hij)

theorem one_le_g {D : D7} (X : HidaSetting D) : 1 ≤ X.B.g := by
  rw [X.g_eq]
  exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (D.host.g_prime 0).ne_zero (D.host.g_prime 1).ne_zero)

theorem scale_pin : ∀ (D : D7) (X : HidaSetting D) (u u' : D.what₂.Word), ∃ s : X.B.I.Ginf → NNReal, (∀ γ, Formalism.L2.SG.RealObj.RegX X u u' γ → s γ = 1) ∧ (∀ γ, 0 < s γ) ∧ (∀ γ, s γ ≤ 1) ∧ ∀ w : Point D.host.E (D.R.rS + 1), (∃ g, Formalism.L2.SG.RealObj.IsPtRep X u u' w g) → (s (Formalism.L2.SG.RealObj.gamW X u u' w) : ℝ) = (((X.B.g : ℝ) ^ (D.R.f * Fintype.card (Formalism.L2.SG.RealObj.FreeE w)))⁻¹) := by
  intro D X u u'
  have hg : (1 : NNReal) ≤ (X.B.g : NNReal) := by exact_mod_cast one_le_g X
  let sc : X.B.I.Ginf → NNReal := fun γ =>
    if h : ∃ w, IsPtRep X u u' w γ then ((X.B.g : NNReal) ^ (D.R.f * Fintype.card (FreeE h.choose)))⁻¹ else 1
  refine ⟨sc, ?_, ?_, ?_, ?_⟩
  · intro γ hγ
    simp only [sc]
    split_ifs with h
    · have := isEmpty_freeE_of_reg X u u' _ γ hγ h.choose_spec
      simp [Fintype.card_eq_zero]
    · rfl
  · intro γ
    simp only [sc]
    split_ifs
    · exact inv_pos.mpr (pow_pos (lt_of_lt_of_le one_pos hg) _)
    · exact one_pos
  · intro γ
    simp only [sc]
    split_ifs
    · exact inv_le_one_of_one_le₀ (one_le_pow₀ hg)
    · exact le_rfl
  · rintro w ⟨γ0, hγ0⟩
    have hex0 : ∃ γ, IsPtRep X u u' w γ := ⟨γ0, hγ0⟩
    have hw : IsPtRep X u u' w (gamW X u u' w) := by
      unfold gamW
      rw [dif_pos hex0]
      exact hex0.choose_spec
    have hex : ∃ w', IsPtRep X u u' w' (gamW X u u' w) := ⟨w, hw⟩
    simp only [sc, dif_pos hex]
    rw [ptRep_unique X u u' hex.choose_spec hw]
    push_cast
    rfl

end GlobalTheory.PinScale
end
end

section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FrameIsom

theorem frameOK_mapLF : ∀ (D : D7) (γ : (VS D).V ≃ₗ[D.host.E] (VS D).V), γ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT →
    ∀ (Λ₁ Λ₂ : Submodule (𝓞 D.host.E) (VS D).V), Formalism.HermitianLatticesTheory.gmap γ Λ₁ = Λ₂ →
    ∀ (T : D.host.E) (F : LFlag (D.sp.Y 0) D.R.rS T), FrameOK D Λ₁ F → FrameOK D Λ₂ (mapLF γ F) := by
  intro D γ hγ Λ₁ Λ₂ hΛ T F hF
  subst hΛ
  have e : mapLF γ F = PI.RepsIndep.Tr.mapL γ hγ F := by
    unfold mapLF
    rw [dite_eq_left hγ]
    rfl
  rw [e]
  exact PI.RepsIndep.Tr.FrameOK_map hγ hF

end GlobalTheory.FrameIsom
end

section

open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.GamRat

theorem gam_rat : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (γ : Gam X u), ∃ γ₀ : GL (Fin X.B.I.n) X.B.I.E, γ₀ ∈ Formalism.UG.UJ (starRingEnd X.B.I.E) X.B.I.J ∧ (∀ v, uMat ((γ : X.B.I.GA).1 v) = (X.B.I.P v)⁻¹ * (γ₀ : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E).map (X.B.I.φ v) * X.B.I.P v) ∧ X.B.I.fmat (γ : X.B.I.GA).2 = (γ₀ : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E).map (Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F)) ∧ ∀ x ∈ fixSet X u, (γ₀ : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) *ᵥ x = x := by
  intro D X u γ
  obtain ⟨hGF, hH⟩ := Subgroup.mem_inf.1 γ.2
  obtain ⟨γ₀, hU, h1, h2⟩ := (Formalism.MainNotions.LeviCoordinates.rr_mem_GF _ _).1 hGF
  refine ⟨γ₀, hU, h1, h2, ?_⟩
  intro x hx
  have hf := (Subgroup.mem_prod.1 hH).2 x hx
  rw [h2] at hf
  have : Nontrivial (Af X.B.I.F) := by
    obtain ⟨P, hP⟩ := Ideal.exists_maximal (𝓞 X.B.I.F)
    let w : IsDedekindDomain.HeightOneSpectrum (𝓞 X.B.I.F) :=
      ⟨P, hP.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hP (RingOfIntegers.not_isField _)⟩
    refine ⟨0, 1, fun h => ?_⟩
    have h0 : (0 : w.adicCompletion X.B.I.F) = 1 := congrArg (fun a : Af X.B.I.F => a w) h
    exact zero_ne_one h0
  funext i
  apply Formalism.UG.P.inclE_injective X.B.I.F X.B.I.E (Af X.B.I.F)
  calc Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F) (((γ₀ : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) *ᵥ x) i)
      = ((γ₀ : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E).map (Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F)) *ᵥ
          (Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F) ∘ x)) i := RingHom.map_mulVec _ _ _ _
    _ = _ := congrFun hf i

end GlobalTheory.GamRat
end

section

open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.St

theorem rat_unitary_fixing_mem_gam : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (γ₀ : GL (Fin X.B.I.n) X.B.I.E), γ₀ ∈ Formalism.UG.UJ (starRingEnd X.B.I.E) X.B.I.J → (∀ x ∈ fixSet X u, (γ₀ : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) *ᵥ x = x) → ∃ γ : Gam X u, (∀ v, uMat ((γ : X.B.I.GA).1 v) = (X.B.I.P v)⁻¹ * (γ₀ : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E).map (X.B.I.φ v) * X.B.I.P v) ∧ X.B.I.fmat (γ : X.B.I.GA).2 = (γ₀ : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E).map (Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F)) := by
  intro D X u γ₀ hγ₀ hfix
  have hs : (Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F)).comp (starRingEnd X.B.I.E) =
      (Formalism.UG.sigR X.B.I.cm.sig (Af X.B.I.F)).comp (Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F)) := by
    ext e
    exact (PI.UnitaryGroupMassFormula.InHHClassFin.rt_sig X.B.I e).symm
  have hm := Formalism.UG.P.bc_mem _ _ _ hs X.B.I.J γ₀ hγ₀
  let g : X.B.I.Gf := ⟨_, hm⟩
  have hg : X.B.I.fmat g = (γ₀ : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E).map
      (Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F)) :=
    Formalism.UG.P.bc_coe _ γ₀
  have hinf : (fun v => PI.UnitaryGroupMassFormula.InHHClassFin.rtReal X.B.I γ₀ hγ₀ v) ∈ Hinf X u := by
    intro v y hy
    have hP : X.B.I.P v * (X.B.I.P v)⁻¹ = 1 :=
      Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp (X.B.I.P_unit v))
    show uMat (PI.UnitaryGroupMassFormula.InHHClassFin.rtReal X.B.I γ₀ hγ₀ v) *ᵥ
        ((X.B.I.P v)⁻¹ *ᵥ fun i => X.B.I.φ v (y i)) = (X.B.I.P v)⁻¹ *ᵥ fun i => X.B.I.φ v (y i)
    rw [PI.UnitaryGroupMassFormula.InHHClassFin.rt_uMat, Matrix.mulVec_mulVec, Matrix.mul_assoc _ (X.B.I.P v), hP,
      Matrix.mul_one, ← Matrix.mulVec_mulVec]
    congr 1
    funext i
    exact (RingHom.map_mulVec (X.B.I.φ v) (γ₀ : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) y i).symm.trans
      (congrArg (X.B.I.φ v) (congrFun (hfix y hy) i))
  have hfin : g ∈ Hfin X u := by
    intro y hy
    rw [hg]
    funext i
    exact (RingHom.map_mulVec (Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F))
      (γ₀ : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) y i).symm.trans
      (congrArg _ (congrFun (hfix y hy) i))
  refine ⟨⟨(fun v => PI.UnitaryGroupMassFormula.InHHClassFin.rtReal X.B.I γ₀ hγ₀ v, g), ?_⟩, ?_, ?_⟩
  · show _ ∈ Formalism.MainNotions.LeviCoordinates.rr_GF X.B.I ⊓ (Hinf X u).prod (Hfin X u)
    refine Subgroup.mem_inf.2 ⟨?_, Subgroup.mem_prod.2 ⟨hinf, hfin⟩⟩
    exact ⟨γ₀, hγ₀, fun v => PI.UnitaryGroupMassFormula.InHHClassFin.rt_uMat X.B.I γ₀ hγ₀ v, hg⟩
  · intro v
    exact PI.UnitaryGroupMassFormula.InHHClassFin.rt_uMat X.B.I γ₀ hγ₀ v
  · exact hg

end GlobalTheory.St
end

section

open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc GlobalTheory.HL
open scoped Pointwise ENNReal Classical

theorem _root_.GlobalTheory.T.hermitianDoubleCoset_amplitude_bound_local : ∀ (C : ℝ), 39 ≤ C → ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) (r k : ℕ) (P : LocNG.FPair H r), 4 * r + 7 ≤ k → Module.finrank E V = k + 2 * r + 1 → P.RelG (LocNG.theta M) → LocNG.NGAt k P C := by
  first | exact @GlobalTheory.HL.AbstractBound.ngAt | exact GlobalTheory.HL.AbstractBound.ngAt | (intros; apply GlobalTheory.HL.AbstractBound.ngAt <;> assumption)
end
