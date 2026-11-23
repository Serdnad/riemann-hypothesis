module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle023
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.PtCellUniq
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.TermDefPf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.DoubleCosetSingleUnfolding
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.RegroupPf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.EnergyAbs
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.RealObj
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.InfCut
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.IdMeetVolSteps
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.RegroupPfOrbitAlg
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle022
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InHHDef
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.HermitianETransportInvariant
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InHHGamUnipKu
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.Bundle005
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.NilradicalLatticeZMemSpan
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle015
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.LevelSubgroupProperties
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle021
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle005
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InHHFinOrd
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.IdBlocks

@[expose] public section

section

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S
open scoped ComplexConjugate
open Matrix

namespace Formalism.L2.SG.RealObj.HermitianSumRootCoordinateFrames

open Formalism.L2.SG.RealObj Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj.HermitianBlockSpans Formalism.L2.SG.RealObj.RootCoordinateFrames

theorem nxt_eq {n r : ℕ} (e : Fin r → Fin n → ℂ) (z : Fin n → ℂ) (a : Fin r) : nxt e z a = fam e z a.succ := by
  unfold nxt fam
  split_ifs with h
  · have hs : a.succ = Fin.castSucc ⟨a.1 + 1, h⟩ := Fin.ext (by simp)
    rw [hs, Fin.snoc_castSucc]
  · have hs : a.succ = Fin.last r := Fin.ext (by simp; omega)
    rw [hs, Fin.snoc_last]

theorem hJ_sum_left {n m : ℕ} (ε : Fin n → Bool) (c : Fin m → ℂ) (v : Fin m → Fin n → ℂ) (w : Fin n → ℂ) :
    hJ ε (∑ i, c i • v i) w = ∑ i, star (c i) * hJ ε (v i) w := by
  unfold hJ
  rw [star_sum, sum_dotProduct]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [star_smul, smul_dotProduct, smul_eq_mul]

private theorem hJ_fintype_sum_smul_right {n : ℕ} {ι : Type} [Fintype ι] (ε : Fin n → Bool) (x : Fin n → ℂ)
    (Q : ι → ℂ) (y : ι → Fin n → ℂ) :
    hJ ε x (∑ c, Q c • y c) = ∑ c, Q c * hJ ε x (y c) := by
  unfold hJ
  rw [Matrix.mulVec_sum, dotProduct_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]

theorem RootCoordFrame_holds : RootCoordFrame := by
  intro n r ε e f z hfe hfz g P hP a
  unfold rootCoord
  rw [nxt_eq, hP, hJ_fintype_sum_smul_right]
  rw [Finset.sum_eq_single a.castSucc]
  · rw [show fam e z a.castSucc = e a from by unfold fam; exact Fin.snoc_castSucc _ _ _, hfe, if_pos rfl, mul_one]
  · intro c _ hc
    refine Fin.lastCases ?_ (fun b hb => ?_) c hc
    · intro _
      rw [show fam e z (Fin.last r) = z from by unfold fam; exact Fin.snoc_last _ _, hfz, mul_zero]
    · rw [show fam e z b.castSucc = e b from by unfold fam; exact Fin.snoc_castSucc _ _ _, hfe]
      have hab : a ≠ b := fun h => hb (by rw [h])
      rw [if_neg hab, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem ZhatNAct_holds : ZhatNAct := by
  intro n r ε f f' s si s' g P P' hsi hinv hP hP'
  have hs : s * si = 1 := mul_eq_one_comm.mp hsi
  ext a b
  have h1 : (si * g * s') *ᵥ f' b = si *ᵥ (g *ᵥ (s' *ᵥ f' b)) := by
    simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]
  have h2 : hJ ε (f a) (si *ᵥ (g *ᵥ (s' *ᵥ f' b))) = hJ ε (s *ᵥ f a) (g *ᵥ (s' *ᵥ f' b)) := by
    rw [← hinv (f a) (si *ᵥ _), Matrix.mulVec_mulVec, hs, Matrix.one_mulVec]
  show hJ ε (f a) ((si * g * s') *ᵥ f' b) = _
  rw [h1, h2, hP a, hP' b, hJ_sum_left, Matrix.mulVec_sum]
  simp only [Matrix.mulVec_smul, hJ_fintype_sum_smul_right, Matrix.mul_apply, Matrix.map_apply,
    Matrix.transpose_apply, Zhat, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun c _ => ?_
  ring

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem FrameAtV_holds : FrameAtV := by
  intro D X u v
  have hc : ∀ p q : (VS D).V, hJ (X.B.I.ε v) (rv X.B.I v (X.crd p)) (rv X.B.I v (X.crd q)) =
      embS D (X.pl v) ((VS D).hT p q) := fun p q => Formalism.L2.SG.PoincareInHH.Cut.hJ_crd (X := X) v p q
  have hs : ∀ p q : (VS D).V, (VS D).hT q p = starRingEnd D.host.E ((VS D).hT p q) := by
    intro p q
    first
    | exact ((VS D).herm.eq p q).symm
    | exact ((VS D).herm p q).symm
  simp only [HidaSetting.eR, HidaSetting.fR, HidaSetting.zR, hc]
  refine ⟨fun a b => by rw [X.ee a b, map_zero], fun a b => by rw [X.ff a b, map_zero],
    fun a b => ?_, fun a b => ?_,
    fun a => ⟨by rw [(X.zu_orth u a).1, map_zero], by rw [(X.zu_orth u a).2, map_zero]⟩, ?_, ?_⟩
  · rw [X.ef a b]
    split_ifs <;> simp
  · rw [hs, X.ef b a]
    by_cases h : a = b
    · subst h
      simp
    · rw [if_neg (Ne.symm h), if_neg h, map_zero, map_zero]
  · rw [X.zu_norm u, map_neg, map_natCast]
    simp [Tw]
  · unfold Tw
    exact_mod_cast (D.mem u).A.T_prime.ne_zero

end Formalism.L2.SG.RealObj.HermitianSumRootCoordinateFrames
end
end

section

noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.TermDef

namespace Formalism.L2.SG.RowsAbsX

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem atPt_uniq {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ}
    (Λ : Submodule (𝓞 E) S.V) {T T' : E} (F : LFlag S r T) (P : LFlag S r T' → Prop) (t : TermQ Λ F P)
    (w w' : Point E (r + 1)) (h : AtPt Λ F P t w) (h' : AtPt Λ F P t w') : w = w' := by
  obtain ⟨F₁, ⟨h₁, e₁⟩, -, c₁⟩ := h
  obtain ⟨F₂, ⟨h₂, e₂⟩, -, c₂⟩ := h'
  have hq : Quot.mk (Rel Λ F P) ⟨F₁, h₁⟩ = Quot.mk (Rel Λ F P) ⟨F₂, h₂⟩ := e₁.trans e₂.symm
  have hg := Quot.eqvGen_exact hq
  have inv : ∀ x y : Carrier P, Relation.EqvGen (Rel Λ F P) x y → ∀ v : Point E (r + 1),
      (IsInCell (ZhatOM (ZhatL F x.1)) v ↔ IsInCell (ZhatOM (ZhatL F y.1)) v) := by
    intro x y hxy
    induction hxy with
    | rel x y hr => exact Formalism.L2.SG.Pf.cell_function_holds Λ F P x y hr
    | refl x => exact fun v => Iff.rfl
    | symm x y _ ih => exact fun v => (ih v).symm
    | trans x y z _ _ ih₁ ih₂ => exact fun v => (ih₁ v).trans (ih₂ v)
  exact Formalism.L2.SG.PtCell.isInCell_uniq ((inv _ _ hg w).1 c₁) c₂

variable {D : D7} (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word)

theorem ptUniq_holds : PtUniq X Y u u' := fun t w w' h h' => atPt_uniq _ _ _ t.cls w w' h h'

end Formalism.L2.SG.RowsAbsX
end
end

section

noncomputable section

open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.TermOp Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.Full

namespace Formalism.L2.SG.Pf.SlabMajPt

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D}

theorem col_val (hK : X.LevelSubgroupCharacter) (w : D.what₂.Word) (T : Cu X w hK) (ξ : X.Vpi w) (γ : Gam X w) (x : Hfin X w)
    (κ : Ku X w hK) :
    (T : X.Vpi w →ₗ[ℂ] (Hinf X w × Hfin X w → ℂ)) ξ (1, iotaF X w γ * x * (κ : Hfin X w)) =
      ((psiK X w hK κ : ℂˣ) : ℂ) *
        (T : X.Vpi w →ₗ[ℂ] (Hinf X w × Hfin X w → ℂ)) (piRep X w (iotaI X w γ)⁻¹ ξ) (1, x) := by
  obtain ⟨hF, hE⟩ := T.2
  obtain ⟨hL, hR⟩ := hF ξ
  have e1 : ((1 : Hinf X w), iotaF X w γ * x * (κ : Hfin X w)) =
      ((1 : Hinf X w), iotaF X w γ * x) * ((1 : Hinf X w), (κ : Hfin X w)) := by simp
  have e2 : ((1 : Hinf X w), iotaF X w γ * x) = (iotaI X w γ, iotaF X w γ) * ((iotaI X w γ)⁻¹, x) := by simp
  have e3 : ((iotaI X w γ)⁻¹, x) = ((1 : Hinf X w), x) * ((iotaI X w γ)⁻¹, (1 : Hfin X w)) := by simp
  rw [e1, hR, e2, hL, e3, ← hE]

theorem norm_psiK (hK : X.LevelSubgroupCharacter) (w : D.what₂.Word) (κ : Ku X w hK) : ‖((psiK X w hK κ : ℂˣ) : ℂ)‖ = 1 :=
  hK.2.2.2.2 _ κ.2

theorem col_lower (Y : Full X) (w : D.what₂.Word) :
    ∃ (n : ℕ) (T : Fin n → Cu X w Y.hK), ∀ (ξ : X.Vpi w) (h : Hfin X w),
      ‖ξ‖ₑ ≤ ∑ i, ‖(T i : X.Vpi w →ₗ[ℂ] (Hinf X w × Hfin X w → ℂ)) ξ (1, h)‖ₑ := by
  have hst : Formalism.L2.SG.ColsDim.StabTriv (iotaF X w) (Ku X w Y.hK) :=
    Formalism.L2.SG.PoincareInHH.Cut.neatKu_of_gamUnipKu X w Y.hK (Formalism.L2.SG.PoincareInHH.Cut.latOfLattice_holds X w)
      (Formalism.L2.SG.PoincareInHH.Cut.gamUnipKu_holds X w Y.hK)
  have hfin : Finite (Formalism.L2.SG.ColsDim.Classes (iotaF X w) (Ku X w Y.hK)) := by
    refine Finite.of_surjective
      (fun ρ : (Y.cs w).Cl => DoubleCoset.mk (iotaF X w).range (Ku X w Y.hK) ((Y.cs w).h ρ)) ?_
    intro c
    induction c using Quotient.inductionOn' with
    | h g =>
      obtain ⟨ρ, ⟨γ, κ, hg⟩, _⟩ := Y.colReps w g
      refine ⟨ρ, ?_⟩
      show DoubleCoset.mk _ _ _ = DoubleCoset.mk _ _ g
      rw [DoubleCoset.eq]
      exact ⟨iotaF X w γ, ⟨γ, rfl⟩, κ, κ.2, hg⟩
  have := Fintype.ofFinite (Formalism.L2.SG.ColsDim.Classes (iotaF X w) (Ku X w Y.hK))
  obtain ⟨e, he⟩ := Formalism.L2.SG.ColsDim.columns_decomposition (Gam X w) (Hinf X w) (Hfin X w) ℂ (X.Vpi w) (iotaI X w)
    (iotaF X w) (Ku X w Y.hK) (psiK X w Y.hK) (piRep X w) (fun c => c.out) (fun c => DoubleCoset.out_eq' c) hst
  obtain ⟨b, -⟩ : ∃ b : OrthonormalBasis (Fin (Module.finrank ℂ (X.Vpi w))) ℂ (X.Vpi w), True :=
    ⟨stdOrthonormalBasis ℂ (X.Vpi w), trivial⟩
  let ι := Formalism.L2.SG.ColsDim.Classes (iotaF X w) (Ku X w Y.hK) × Fin (Module.finrank ℂ (X.Vpi w))
  let f : ι → Cu X w Y.hK := fun p => e.symm (fun c => if c = p.1 then innerₛₗ ℂ (b p.2) else 0)
  have hf : ∀ p ξ, (f p : X.Vpi w →ₗ[ℂ] (Hinf X w × Hfin X w → ℂ)) ξ (1, p.1.out) = inner ℂ (b p.2) ξ := by
    intro p ξ
    rw [← he]
    simp only [LinearEquiv.apply_symm_apply]
    rfl
  refine ⟨Fintype.card ι, fun i => f ((Fintype.equivFin ι).symm i), fun ξ h => ?_⟩
  obtain ⟨c, hc⟩ : ∃ c, c = DoubleCoset.mk (iotaF X w).range (Ku X w Y.hK) h := ⟨_, rfl⟩
  obtain ⟨g, ⟨γ, rfl⟩, κ, hκ, hh⟩ := (@DoubleCoset.eq _ _ _ _ c.out h).1 (by rw [DoubleCoset.out_eq', hc])
  obtain ⟨ξ', hξ'⟩ : ∃ ξ', ξ' = piRep X w (iotaI X w γ)⁻¹ ξ := ⟨_, rfl⟩
  have hn : ‖ξ'‖ = ‖ξ‖ := by
    have h2 : inner ℂ ξ' ξ' = inner ℂ ξ ξ := by
      rw [hξ']
      exact (X.piU_rep w).2.2.1 _ (hinf_le_sinf X w _ ((iotaI X w γ)⁻¹).2) ξ ξ
    rw [norm_eq_sqrt_re_inner (𝕜 := ℂ), norm_eq_sqrt_re_inner (𝕜 := ℂ) ξ, h2]
  have hval : ∀ j, ‖(f (c, j) : X.Vpi w →ₗ[ℂ] (Hinf X w × Hfin X w → ℂ)) ξ (1, h)‖ₑ = ‖inner ℂ (b j) ξ'‖ₑ := by
    intro j
    rw [hh, col_val Y.hK w (f (c, j)) ξ γ c.out ⟨κ, hκ⟩, ← hξ', hf (c, j) ξ', enorm_mul,
      ← ofReal_norm (((psiK X w Y.hK ⟨κ, hκ⟩ : ℂˣ) : ℂ)), norm_psiK, ENNReal.ofReal_one, one_mul]
  calc ‖ξ‖ₑ = ‖ξ'‖ₑ := by rw [← ofReal_norm, ← ofReal_norm, hn]
    _ = ‖∑ j, inner ℂ (b j) ξ' • b j‖ₑ := by rw [b.sum_repr']
    _ ≤ ∑ j, ‖inner ℂ (b j) ξ' • b j‖ₑ := enorm_sum_le _ _
    _ = ∑ j, ‖inner ℂ (b j) ξ'‖ₑ := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [enorm_smul, ← ofReal_norm (b j), b.orthonormal.1 j, ENNReal.ofReal_one, mul_one]
    _ = ∑ j, ‖(f (c, j) : X.Vpi w →ₗ[ℂ] (Hinf X w × Hfin X w → ℂ)) ξ (1, h)‖ₑ :=
        Finset.sum_congr rfl fun j _ => (hval j).symm
    _ ≤ ∑ p : ι, ‖(f p : X.Vpi w →ₗ[ℂ] (Hinf X w × Hfin X w → ℂ)) ξ (1, h)‖ₑ := by
        rw [Fintype.sum_prod_type]
        exact Finset.single_le_sum (f := fun c' => ∑ j, ‖(f (c', j) : X.Vpi w →ₗ[ℂ] (Hinf X w × Hfin X w → ℂ)) ξ (1, h)‖ₑ)
          (fun _ _ => bot_le) (Finset.mem_univ c)
    _ = ∑ i, ‖(f ((Fintype.equivFin ι).symm i) : X.Vpi w →ₗ[ℂ] (Hinf X w × Hfin X w → ℂ)) ξ (1, h)‖ₑ :=
        (Equiv.sum_comp (Fintype.equivFin ι).symm
          (fun p => ‖(f p : X.Vpi w →ₗ[ℂ] (Hinf X w × Hfin X w → ℂ)) ξ (1, h)‖ₑ)).symm

theorem ph_lower (Y : Full X) (w : D.what₂.Word) {n : ℕ} (T : Fin n → Cu X w Y.hK)
    (hT : ∀ (ξ : X.Vpi w) (h : Hfin X w),
      ‖ξ‖ₑ ≤ ∑ i, ‖(T i : X.Vpi w →ₗ[ℂ] (Hinf X w × Hfin X w → ℂ)) ξ (1, h)‖ₑ)
    (x : X.B.I.Ginf) (h : Hfin X w) (k : X.B.I.Gf) (hk : k ∈ X.K2) :
    ‖X.Wu w x‖ₑ ≤ ∑ i, ‖Ph X w Y.hK (T i) (x, (h : X.B.I.Gf) * X.xu w * k)‖ₑ := by
  refine (hT (X.Wu w x) h).trans (le_of_eq (Finset.sum_congr rfl fun i _ => ?_))
  rw [Formalism.L2.SG.Pf.RegroupPf.ph_col Y.hK (Formalism.L2.SG.Pf.phWellDef_holds X w) (T i) x h k hk, enorm_mul,
    ← ofReal_norm (X.chi2 k), Y.hK.2.2.2.2 k hk, ENNReal.ofReal_one, one_mul]

theorem pointwise_majorant_by_columns : Formalism.L2.SG.Pf.Slab.MajPtC := by
  intro D X Y u u'
  obtain ⟨n, T, hT⟩ := col_lower Y u
  obtain ⟨n', T', hT'⟩ := col_lower Y u'
  refine ⟨n, n', T, T', 1, ENNReal.one_ne_top, fun t x => ?_⟩
  obtain ⟨h, κ, hκ, he⟩ := term_supp Y u u' t
  have h1 := ph_lower Y u T hT x ((Y.cs u).h ((Y.cs u).base t.lam)) 1 Y.hK.1
  have h2 := ph_lower Y u' T' hT' (t.pt.1⁻¹ * x) h κ hκ
  have hb : t.pt⁻¹ * (x, Formalism.L2.SG.Pf.Slab.aB Y u t.lam) = (t.pt.1⁻¹ * x, (h : X.B.I.Gf) * X.xu u' * κ) :=
    Prod.ext rfl he
  have ha : (x, Formalism.L2.SG.Pf.Slab.aB Y u t.lam) =
      (x, ((Y.cs u).h ((Y.cs u).base t.lam) : X.B.I.Gf) * X.xu u * 1) := by
    rw [mul_one]; rfl
  rw [hb, ha, one_mul]
  exact (mul_le_mul' h1 h2).trans_eq (Finset.sum_mul_sum _ _ _ _)

end Formalism.L2.SG.Pf.SlabMajPt
end
end

section

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S
open scoped InnerProductSpace ComplexConjugate ENNReal

namespace Formalism.L2.SG.RealObj.EnergyInst

open Formalism.L2.SG.RealObj Formalism.L2.SG.Pf.EnergyAbs

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def tauU {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u : D.what₂.Word) (s : X.B.I.Ginf) : X.Vpi u →L[ℂ] X.Vpi u :=
  X.psiInfU u s • X.piU u s

def StepSchurG : Prop :=
  ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D),
    IsUnitRep X.B.σs ∧ IsSchur (Formalism.L2.SG.ProjRows.muInf X.B.I) X.B.σs (degX X) ∧ ‖X.B.tens X.B.w‖ = 1 ∧
      ∀ y : X.B.I.Ginf, (Formalism.L2.SG.ProjRows.phInf X.B.I X.B.σ X.B.w X.dv y) =
        ((degX X : ℝ) : ℂ) * conj ⟪X.B.tens X.B.w, X.B.σs y (X.B.tens X.B.w)⟫_ℂ

def StepSubG : Prop :=
  ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u : D.what₂.Word),
    IsHaarSub (X.SinfU u) (muS X u) ∧ IsFolner (X.SinfU u) (muS X u) ∧
      tauU X u 1 = 1 ∧ (∀ s ∈ X.SinfU u, ∀ t ∈ X.SinfU u, tauU X u (s * t) = tauU X u s * tauU X u t) ∧
      SFinite (X.nuQ u)

def StepSection : Prop :=
  ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word) (sc : ℝ), 0 < sc →
    ∃ h : Cinf X → X.B.I.Ginf, Measurable h ∧ ∀ c ∈ Good X u u', HasDiag X u u' sc c (h c)

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D)

theorem tauU_unit (u : D.what₂.Word) (s : X.B.I.Ginf) (hs : s ∈ X.SinfU u) (a b : X.Vpi u) :
    ⟪tauU X u s a, tauU X u s b⟫_ℂ = ⟪a, b⟫_ℂ := by
  simp only [tauU, ContinuousLinearMap.smul_apply, inner_smul_left, inner_smul_right, (X.piU_rep u).2.2.1 s hs]
  rw [← mul_assoc, Complex.mul_conj', Formalism.L2.SG.RealObj.InfCut.norm_psiInfU]
  simp

theorem isWAbs_of (hS : StepSchurG) (hG : StepSubG) (u : D.what₂.Word) :
    IsWAbs (Formalism.L2.SG.ProjRows.muInf X.B.I) X.B.σs (degX X) (X.B.tens X.B.w) (X.SinfU u) (tauU X u)
      (X.nuQ u) (X.Wu u) := by
  obtain ⟨-, -, -, hph⟩ := hS D X
  obtain ⟨-, -, h1, hmul, -⟩ := hG D X u
  have hW := X.Wu_spec u
  refine ⟨h1, hmul, fun s hs a b => tauU_unit X u s hs a b, fun s hs x => ?_, hW.2.2.1, fun x => ?_,
    hW.2.2.2.1, hW.2.2.2.2⟩
  · rw [hW.1 s hs x]; rfl
  · obtain ⟨hi, he⟩ := hW.2.1 x
    have e : (fun y => (((degX X : ℝ) : ℂ) * conj ⟪X.B.tens X.B.w, X.B.σs y (X.B.tens X.B.w)⟫_ℂ) • X.Wu u (x * y)) =
        fun y => Formalism.L2.SG.ProjRows.phInf X.B.I X.B.σ X.B.w X.dv y • X.Wu u (x * y) :=
      funext fun y => by rw [hph y]
    rw [e]
    exact ⟨hi, he⟩

theorem inner_transfer (hG : StepSubG) (u u' : D.what₂.Word) (φ : X.B.I.Ginf → ℝ≥0∞) (hφ : Measurable φ)
    (γ γ' : X.B.I.Ginf) (a : X.B.I.Ginf) (ha : a ∈ X.SinfU u) (b : X.B.I.Ginf) (hb : b ∈ X.SinfU u')
    (hγ : γ' = a * γ * b⁻¹) :
    ∫⁻ s, ∫⁻ s', φ (s * γ' * s'⁻¹) ∂(muS X u') ∂(muS X u) = ∫⁻ s, ∫⁻ s', φ (s * γ * s'⁻¹) ∂(muS X u') ∂(muS X u) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, hR, -⟩ := (hG D X u).1
  obtain ⟨-, -, -, -, -, -, -, -, -, hR', -⟩ := (hG D X u').1
  subst hγ
  have hin : ∀ s, ∫⁻ s', φ (s * (a * γ * b⁻¹) * s'⁻¹) ∂(muS X u') = ∫⁻ s', φ (s * a * γ * s'⁻¹) ∂(muS X u') := by
    intro s
    have e : ∀ s', s * (a * γ * b⁻¹) * s'⁻¹ = s * a * γ * (MeasurableEquiv.mulRight b s')⁻¹ := by
      intro s'
      simp only [MeasurableEquiv.coe_mulRight]
      group
    simp_rw [e]
    rw [← lintegral_map_equiv (fun t => φ (s * a * γ * t⁻¹)) (MeasurableEquiv.mulRight b),
      MeasurableEquiv.coe_mulRight, hR' b hb]
  simp_rw [hin]
  have e2 : ∀ s, (∫⁻ s', φ (s * a * γ * s'⁻¹) ∂(muS X u')) =
      (fun t => ∫⁻ s', φ (t * γ * s'⁻¹) ∂(muS X u')) (MeasurableEquiv.mulRight a s) := by
    intro s
    simp only [MeasurableEquiv.coe_mulRight]
  simp_rw [e2]
  rw [← lintegral_map_equiv (fun t => ∫⁻ s', φ (t * γ * s'⁻¹) ∂(muS X u')) (MeasurableEquiv.mulRight a),
    MeasurableEquiv.coe_mulRight, hR a ha]

end Formalism.L2.SG.RealObj.EnergyInst
end
end

section

noncomputable section

namespace Formalism.L2.SG.Pf.IdMeet

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open scoped Classical ENNReal
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat
open Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.TermOp Formalism.L2.SG.TermOp.IdBlocks Formalism.L2.SG.Full
  Formalism.L2.SG.PoincareInHH.Cut

theorem mem_gcS {D : D7} (X : HidaSetting D) (u : D.what₂.Word) (hK : X.LevelSubgroupCharacter) (c : X.B.I.Gf) (s : X.B.I.Ginf) :
    s ∈ GcS X u hK c ↔ ∃ γ : X.B.I.GA, γ ∈ X.B.I.GFset ∧ γ.1 = s ∧ γ.1 ∈ X.NinfU u ∧ γ.2 ∈ X.NfinU u ∧
      c⁻¹ * γ.2 * c ∈ X.K2 := by
  constructor
  · rintro ⟨γ, hγ, rfl⟩
    obtain ⟨hG, hP⟩ := Subgroup.mem_inf.1 hγ
    obtain ⟨h1, h2⟩ := Subgroup.mem_prod.1 hP
    obtain ⟨hN, hk⟩ := Subgroup.mem_inf.1 h2
    obtain ⟨k, hk, hke⟩ := Subgroup.mem_map.1 hk
    refine ⟨γ, hG, rfl, h1, hN, ?_⟩
    have : γ.2 = c * k * c⁻¹ := by rw [← hke]; rfl
    rw [this]
    have : c⁻¹ * (c * k * c⁻¹) * c = k := by group
    rw [this]; exact hk
  · rintro ⟨γ, hG, rfl, h1, hN, hk⟩
    refine ⟨γ, Subgroup.mem_inf.2 ⟨hG, Subgroup.mem_prod.2 ⟨h1, Subgroup.mem_inf.2 ⟨hN, ?_⟩⟩⟩, rfl⟩
    refine Subgroup.mem_map.2 ⟨c⁻¹ * γ.2 * c, hk, ?_⟩
    show c * (c⁻¹ * γ.2 * c) * c⁻¹ = γ.2
    group

theorem noinfEqC_holds : NOinfEqC := by
  intro D X u hK
  ext s
  rw [SetLike.mem_coe, mem_gcS]
  constructor
  · rintro ⟨γ, hG, h1, hN, hF, hk⟩
    exact ⟨γ, hG, h1, hN, hF, hk⟩
  · rintro ⟨γ, hG, h1, hN, hF, hk⟩
    exact ⟨γ, hG, h1, hN, hF, hk⟩

theorem nocolEqC_holds : NOcolEqC := by
  intro D X Y u ρ
  ext s
  rw [SetLike.mem_coe, mem_gcS]
  constructor
  · rintro ⟨x, n, hx, rfl, hn⟩
    exact ⟨x, ratLink_mem X hx, rfl, nLamNinf_holds D X u _ x n hx hn, nLamNfin_holds D X u _ x n hx hn,
      (nilradical_conj_level' D X Y u ρ x n hn hx).1⟩
  · rintro ⟨γ, hG, rfl, hN, hF, hk⟩
    exact Formalism.L2.SG.Pf.SlabCoverPf.nilradical_rational_lattice D X Y u ρ γ (Formalism.L2.SG.Closed.level_subgroup_properties X) hG hN hF hk

theorem gcCountC_holds : GcCountC := by
  intro D X u hK c
  have hR : (RcS X u hK c : Set X.B.I.GA).Countable :=
    (Set.countable_coe_iff.1 (Formalism.MainNotions.LeviCoordinates.rr_GF_countable X.B.I)).mono (fun _ h => (Subgroup.mem_inf.1 h).1)
  have : (GcS X u hK c : Set X.B.I.Ginf).Countable := by
    unfold GcS
    rw [Subgroup.coe_map]
    exact hR.image _
  exact this.to_subtype

theorem conjUC_holds : ConjUC := by
  intro D X u hK g c
  ext x
  simp only [UcS, Subgroup.mem_inf, Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · rintro ⟨hN, k, hk, hke⟩
    refine ⟨(g : X.B.I.Gf)⁻¹ * x * (g : X.B.I.Gf), ⟨?_, k, hk, ?_⟩, ?_⟩
    · have := (nfinConj_holds X u g⁻¹ x hN).1
      simp only [InvMemClass.coe_inv, inv_inv] at this
      exact this
    · rw [← hke]; group
    · group
  · rintro ⟨y, ⟨hN, k, hk, hke⟩, rfl⟩
    refine ⟨(nfinConj_holds X u g y hN).1, k, hk, ?_⟩
    rw [← hke]; group

end Formalism.L2.SG.Pf.IdMeet
end
end

section

namespace Formalism.L2.SG.Pf.RegroupPf

theorem term_carrier_holds : TermCarC :=
  termCarC_of rational_isomorphism_holds reduction_mod_g_holds frame_congruence_holds

end Formalism.L2.SG.Pf.RegroupPf
end
