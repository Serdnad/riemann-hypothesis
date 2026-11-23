module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.PoincareConstantEq
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.UnipBasis
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InHHNeat
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.ChiNCut
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle010
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle011
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.NormCorePsiNatEquiv
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.PhaseAtPf
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.DualCoords
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
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.KExpCut
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InHHCut
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle012
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.PoincareInHH

@[expose] public section

section

noncomputable section

open scoped Classical ComplexConjugate TensorProduct
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Matrix Formalism.L2.SG.TermOp Formalism.L2.SG.HidaSetting
  Formalism.L2.SG.Pf.unitaryCongruence

namespace Formalism.L2.SG.NormCut

section GoodNC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D)

theorem ncong_inv {x : X.B.I.Gf} (hx : x ∈ X.B.I.Kset) (hn : NCong X x) : NCong X x⁻¹ := by
  refine ⟨inv_e X.B.I X.B.g X.e0 hx hn.1, ?_⟩
  rw [inv_id]
  refine neg_mem (pres X.B.I (K_inv X.B.I hx) X.B.g _ _ (sub_Mo X.B.I) ?_ (mL_Mo X.B.I) _ hn.2)
  rintro _ ⟨b, rfl⟩
  exact Mo_mono X.B.I (Set.image_subset_range _ _) (inv_e X.B.I X.B.g X.e0 hx hn.1 b)

theorem hermitian_module_beta_congruence {m : VA X.B.I} (hm : m ∈ Mo X.B.I X.B.g (Set.range X.e0)) (j : Fin D.R.k) :
    ZMod' X.B.I X.B.g (hA X.B.I m (X.bw j)) := by
  rw [hA_symm]
  refine Z_sig X.B.I X.B.g (Z_pair_Mo X (X.vectorsInLattice.2.2 j).1 ?_ _ hm)
  rintro _ ⟨a, rfl⟩
  rw [hA_symm]
  exact Z_sig X.B.I X.B.g ((X.weightVectorsIntegral j).2.2 a).1

theorem par_of_ncong {x : X.B.I.Gf} (hx : x ∈ X.B.I.Kset) (hn : NCong X x) (hni : NCong X x⁻¹) : Par X x := by
  obtain ⟨hE0, hF0, hZ0, hB, hBd⟩ := frame_Lf X
  refine ⟨hx, fun a => ?_, fun j => ?_⟩
  · rw [show X.B.I.fmat x *ᵥ X.e0 a = X.e0 a + (X.B.I.fmat x - 1) *ᵥ X.e0 a by
      rw [Matrix.sub_mulVec, Matrix.one_mulVec]; abel]
    exact add_mem (sub_Mo X.B.I ⟨a, rfl⟩) (Mo_mono X.B.I (Set.image_subset_range _ _) (hn.1 a))
  · refine mem_Mo_eb X (K_mv X.B.I hx (hB j)) (fun a => ?_) ?_ (fun l => ?_)
    · rw [hA_adj]
      refine hermitian_module_beta_congruence X ?_ j
      rw [show X.B.I.fmat x⁻¹ *ᵥ X.e0 a = X.e0 a + (X.B.I.fmat x⁻¹ - 1) *ᵥ X.e0 a by
        rw [Matrix.sub_mulVec, Matrix.one_mulVec]; abel]
      exact add_mem (sub_Mo X.B.I ⟨a, rfl⟩) (Mo_mono X.B.I (Set.image_subset_range _ _) (hni.1 a))
    · rw [hA_adj, show X.B.I.fmat x⁻¹ *ᵥ X.z0 = X.z0 + (X.B.I.fmat x⁻¹ - 1) *ᵥ X.z0 by
        rw [Matrix.sub_mulVec, Matrix.one_mulVec]; abel, hA_add_left]
      exact Z_add X.B.I X.B.g (X.weightVectorsIntegral j).1 (hermitian_module_beta_congruence X hni.2 j)
    · have e : hA X.B.I (X.bw l) (X.B.I.fmat x *ᵥ X.bw j) = 0 := by
        rw [X.bw_w l, X.bw_w j, Matrix.mulVec_smul, hA_smul_left, hA_smul_right]
        have := X.ew_orth
        linear_combination (hA X.B.I (X.bw l) (X.B.I.fmat x *ᵥ X.bw j)) * this
      rw [e]; exact Z_zero X.B.I X.B.g

theorem good_of_ncong {x : X.B.I.Gf} (hx : x ∈ X.B.I.Kset) (hn : NCong X x) : Good X x := by
  have hni := ncong_inv X hx hn
  have hxi : x⁻¹ ∈ X.B.I.Kset := by
    simp only [Formalism.MainNotions.S.AutInst.Kset, Set.mem_setOf_eq] at hx ⊢
    simpa using inv_mem hx
  exact ⟨par_of_ncong X hx hn hni, par_of_ncong X hxi hni (by simpa using hn)⟩

end GoodNC

section AdmParPf

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {u u' : D.what₂.Word}
  {F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)} {F0' : FlagG (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)}
  {what₂ rows' : Finset (Submodule (𝓞 D.host.E) (VS D).V)} (cs : ColSys X u what₂) (cs' : ColSys X u' rows')


variable (F0 F0') in
def TermK : Prop :=
  ∀ t : GTerm X u u' F0 F0' what₂ rows',
    kOf X u u' (cs.h (cs.base t.lam) : X.B.I.Gf) (cs'.h (cs'.base t.lam') : X.B.I.Gf) t.pt ∈ X.B.I.Kset

theorem adm_parity_of_norm (hK : TermK F0 F0' cs cs') (hN : AdmN F0 F0' cs cs') : AdmPar F0 F0' cs cs' := by
  intro t
  exact good_of_ncong _ (hK t) (hN t)

end AdmParPf

end Formalism.L2.SG.NormCut
end
end

section

noncomputable section

open scoped Classical ComplexConjugate ENNReal NNReal
open MeasureTheory

namespace Formalism.L2.SG.Pf.SlabCount

open Formalism.L2.SG.FoldBound Formalism.L2.SG.PoincareSeriesSquareIntegrable NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermOp
  Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.PoincareInHH.Cut Formalism.L2.SG.TermOp.KExpCut Formalism.L2.SG.Full

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def LeviFinC : Prop :=
  ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (Y : Full X) (u' : D.what₂.Word),
    ∃ F : Submodule (𝓞 D.host.E) (VS D).V → Submodule (𝓞 D.host.E) (VS D).V →
        Finset ((VS D).V ≃ₗ[D.host.E] (VS D).V),
      ∀ Λ₁ ∈ Y.what₂ u', ∀ Λ₂ ∈ Y.what₂ u', ∀ (σ : (VS D).V ≃ₗ[D.host.E] (VS D).V) (s : X.B.I.GA),
        RatLink X s σ → σ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT → s ∈ Srat X u' → Formalism.HermitianLatticesTheory.gmap σ Λ₂ = Λ₁ →
          ∃ f ∈ F Λ₁ Λ₂, f⁻¹ * σ ∈ NLam Λ₂ (lf D (X.Fu u'))

theorem tsum_comp_le_of_fibre {ι κ β : Type*} (φ : ι → κ) (g : κ → ℝ≥0∞) (M : ℕ)
    (hfib : ∀ k, ∃ (S : Finset β) (e : ι → β), S.card ≤ M ∧
      ∀ i, φ i = k → e i ∈ S ∧ ∀ j, φ j = k → e i = e j → i = j) :
    ∑' i, g (φ i) ≤ (M : ℝ≥0∞) * ∑' k, g k := by
  rw [← (Equiv.sigmaFiberEquiv φ).tsum_eq, ENNReal.tsum_sigma', ← ENNReal.tsum_mul_left]
  refine ENNReal.tsum_le_tsum fun k => ?_
  obtain ⟨S, e, hS, he⟩ := hfib k
  rw [ENNReal.tsum_eq_iSup_sum]
  refine iSup_le fun s => ?_
  have hc : s.card ≤ M := by
    refine le_trans ?_ hS
    refine Finset.card_le_card_of_injOn (fun i => e (i : ι)) (fun i _ => (he i.1 i.2).1) ?_
    intro i _ j _ hij
    exact Subtype.ext ((he i.1 i.2).2 j.1 j.2 hij)
  calc ∑ i ∈ s, g (φ ((Equiv.sigmaFiberEquiv φ) ⟨k, i⟩))
      = ∑ i ∈ s, g k := Finset.sum_congr rfl fun i _ => by
          show g (φ i.1) = g k
          rw [i.2]
    _ = (s.card : ℝ≥0∞) * g k := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (M : ℝ≥0∞) * g k := by gcongr

end Formalism.L2.SG.Pf.SlabCount
end
end

section

noncomputable section

open scoped Classical
open Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Pf.UnipB Formalism.L2.SG.Pf.Unip

namespace Formalism.L2.SG.TermOp.Vanish

open Formalism.L2.SG.Full

def Gr {D : D7} (X : HidaSetting D) (M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) :
    Matrix (Kap X) (Kap X) X.B.I.E :=
  Bm' X * M * Bm X

def RatApprox : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (M : GL (Fin X.B.I.n) X.B.I.E), M ∈ Formalism.UG.UJ (starRingEnd X.B.I.E) X.B.I.J →
    ∀ k : ℕ, 1 ≤ k → ∀ d : ℕ, 1 ≤ d → ∃ C : ℝ, ∀ P : InfinitePlace X.B.I.F → Matrix (Kap X) (Kap X) ℂ,
      (∀ v, InPat (lvk X) k (P v) ∧
        InPat (lvk X) 1 ((Gr X (↑M⁻¹ : Matrix _ _ _)).map (X.B.I.φ v) * P v * (Gr X (M : Matrix _ _ _)).map (X.B.I.φ v)) ∧
        (P v)ᴴ * JBv X v = -(JBv X v * P v)) →
      ∃ Y : Matrix (Kap X) (Kap X) X.B.I.E, InPat (lvk X) k Y ∧
        InPat (lvk X) 1 (Gr X (↑M⁻¹ : Matrix _ _ _) * Y * Gr X (M : Matrix _ _ _)) ∧ Yᴴ * JB X = -(JB X * Y) ∧
        (∃ A : Matrix (Kap X) (Kap X) (𝓞 X.B.I.E), Y = (d : X.B.I.E) • A.map (fun a => (a : X.B.I.E))) ∧
        ∀ v i j, ‖(Y.map (X.B.I.φ v) - P v) i j‖ ≤ C

def RatMem : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word)
    (t : GTerm X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u')) (M : GL (Fin X.B.I.n) X.B.I.E),
    M ∈ Formalism.UG.UJ (starRingEnd X.B.I.E) X.B.I.J → (∀ y, X.crd (t.lin y) = (M : Matrix _ _ _) *ᵥ X.crd y) →
    ∃ d : ℕ, 1 ≤ d ∧ ∀ Z : Matrix (Kap X) (Kap X) X.B.I.E, InPat (lvk X) 1 Z →
      InPat (lvk X) 1 (Gr X (↑M⁻¹ : Matrix _ _ _) * Z * Gr X (M : Matrix _ _ _)) → Zᴴ * JB X = -(JB X * Z) →
      (∃ A : Matrix (Kap X) (Kap X) (𝓞 X.B.I.E), Z = (d : X.B.I.E) • A.map (fun a => (a : X.B.I.E))) →
      ∃ s ∈ ROinf t, ∀ v, Mv X v s = (cay (2 * D.R.rS + 2) Z).map (X.B.I.φ v)

end Formalism.L2.SG.TermOp.Vanish
end
end

section

noncomputable section

open scoped Classical ComplexConjugate TensorProduct
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Matrix Formalism.L2.SG.TermOp Formalism.L2.SG.HidaSetting
  Formalism.L2.SG.Pf.unitaryCongruence Formalism.L2.SG.PoincareInHH.PoincareSetting

namespace Formalism.L2.SG.NormCut

section ColFreeBij

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} (TR : TypedRed X) {u : D.what₂.Word}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)} (cs : ColSys X u what₂)

def colD (h h' : Hfin X u) : X.B.I.Gf := ((h : X.B.I.Gf) * X.xu u)⁻¹ * ((h' : X.B.I.Gf) * X.xu u)

def LeviOnto : Prop :=
  ∀ (q : {Λ // Λ ∈ what₂}) (s : Iof TR), ∃ h : Hfin X u,
    colD (cs.h (cs.base q.1)) h ∈ X.B.I.Kset ∧ colD h (cs.h (cs.base q.1)) ∈ X.B.I.Kset ∧
      levi TR (colD (cs.h (cs.base q.1)) h) = s

def ColLatRep (hK : X.LevelSubgroupCharacter) : Prop :=
  ∀ (q : {Λ // Λ ∈ what₂}) (h : Hfin X u) (ρ : cs.Cl) (γ : Gam X u) (κ : Ku X u hK),
    colD (cs.h (cs.base q.1)) h ∈ X.B.I.Kset → h = iotaF X u γ * cs.h ρ * (κ : Hfin X u) → cs.lamOf ρ = q.1

theorem UG_mul {x y : Iof TR} (hx : x ∈ UG TR) (hy : y ∈ UG TR) : x * y ∈ UG TR := fun v =>
  Formalism.L2.SG.NormCut.PsiNatEquivPf.isUni_mul (hx v) (hy v)

theorem UG_inv {x : Iof TR} (hx : x ∈ UG TR) : x⁻¹ ∈ UG TR := fun v =>
  Formalism.L2.SG.NormCut.PsiNatEquivPf.isUni_inv (hx v)

theorem colD_mul (h h' h'' : Hfin X u) : colD h h' * colD h' h'' = colD h h'' := by
  unfold colD; group

theorem colD_inv (h h' : Hfin X u) : (colD h h')⁻¹ = colD h' h := by
  unfold colD; group

theorem good_colD {h h' : Hfin X u} (hk : colD h h' ∈ X.B.I.Kset) : Good X (colD h h') :=
  colGood X u h h' hk (by have := K_inv X.B.I hk; rw [colD_inv] at this; exact this)

theorem scOf_eq (ρ : cs.Cl) : scOf TR cs ρ = levi TR (colD (cs.h (cs.base (cs.lamOf ρ))) (cs.h ρ)) := rfl

theorem colD_conj (γ h h' : Hfin X u) : colD h (γ * h) * colD h h' = colD h (γ * h') := by
  unfold colD; simp only [Subgroup.coe_mul]; group

theorem colD_ku (hK : X.LevelSubgroupCharacter) {h h' : Hfin X u} (hm : colD h h' ∈ X.K2) : h⁻¹ * h' ∈ Ku X u hK := by
  show (X.xu u)⁻¹ * ((h⁻¹ * h' : Hfin X u) : X.B.I.Gf) * X.xu u ∈ X.K2
  have e : (X.xu u)⁻¹ * ((h⁻¹ * h' : Hfin X u) : X.B.I.Gf) * X.xu u = colD h h' := by
    unfold colD; simp only [Subgroup.coe_mul, Subgroup.coe_inv]; group
  rw [e]; exact hm

theorem colFreeBij_of (hK : X.LevelSubgroupCharacter) (hR : ColReps hK cs) (hN : Formalism.L2.SG.PoincareInHH.Cut.NeatKu X u hK) (hL : ColLatK cs)
    (hO : LeviOnto TR cs) (hRep : ColLatRep cs hK) (q : {Λ // Λ ∈ what₂}) :
    Function.Bijective (fun x : Aset TR cs q × {ρ : cs.Cl // lamQ cs ρ = q} × UG TR =>
      (x.1 : Iof TR) * scOf TR cs x.2.1.1 * (x.2.2 : Iof TR)) := by
  set hb : Hfin X u := cs.h (cs.base q.1) with hhb
  have hbl : cs.lamOf (cs.base q.1) = q.1 := cs.base_lam _ q.2
  have lamρ : ∀ ρ : {ρ : cs.Cl // lamQ cs ρ = q}, cs.lamOf ρ.1 = q.1 := fun ρ => congrArg Subtype.val ρ.2
  have kK : ∀ ρ : cs.Cl, cs.lamOf ρ = q.1 → colD hb (cs.h ρ) ∈ X.B.I.Kset := fun ρ hρ =>
    hL (cs.base q.1) ρ (hbl.trans hρ.symm)
  have kKi : ∀ ρ : cs.Cl, cs.lamOf ρ = q.1 → colD (cs.h ρ) hb ∈ X.B.I.Kset := fun ρ hρ =>
    hL ρ (cs.base q.1) (hρ.trans hbl.symm)
  have scρ : ∀ ρ : {ρ : cs.Cl // lamQ cs ρ = q}, scOf TR cs ρ.1 = levi TR (colD hb (cs.h ρ.1)) := fun ρ => by
    rw [scOf_eq, lamρ ρ]
  have aK : ∀ γ : Gam X u, ((cs.h (cs.base q.1) : X.B.I.Gf) * X.xu u)⁻¹ * (iotaF X u γ : X.B.I.Gf) *
      ((cs.h (cs.base q.1) : X.B.I.Gf) * X.xu u) = colD hb (iotaF X u γ * hb) := fun γ => by
    unfold colD; rw [hhb, Subgroup.coe_mul]; group
  constructor
  · rintro ⟨⟨a1, ha1⟩, ρ1, w1⟩ ⟨⟨a2, ha2⟩, ρ2, w2⟩ heq
    obtain ⟨γ1, hγ1K, ha1e⟩ := ha1
    obtain ⟨γ2, hγ2K, ha2e⟩ := ha2
    simp only at heq
    rw [aK] at hγ1K hγ2K ha1e ha2e
    rw [ha1e, ha2e, scρ, scρ] at heq
    rw [← levi_mul TR (good_colD hγ1K) (good_colD (kK _ (lamρ ρ1))),
      ← levi_mul TR (good_colD hγ2K) (good_colD (kK _ (lamρ ρ2))), colD_conj, colD_conj] at heq
    have hP1 : colD hb (iotaF X u γ1 * cs.h ρ1.1) ∈ X.B.I.Kset := by
      rw [← colD_conj]; exact K_mul X.B.I hγ1K (kK _ (lamρ ρ1))
    have hP2 : colD hb (iotaF X u γ2 * cs.h ρ2.1) ∈ X.B.I.Kset := by
      rw [← colD_conj]; exact K_mul X.B.I hγ2K (kK _ (lamρ ρ2))
    have hmK : colD (iotaF X u γ1 * cs.h ρ1.1) (iotaF X u γ2 * cs.h ρ2.1) ∈ X.B.I.Kset := by
      rw [← colD_mul _ hb, ← colD_inv]; exact K_mul X.B.I (K_inv X.B.I hP1) hP2
    have hlm : levi TR (colD (iotaF X u γ1 * cs.h ρ1.1) (iotaF X u γ2 * cs.h ρ2.1)) =
        (w1 : Iof TR) * (w2 : Iof TR)⁻¹ := by
      rw [← colD_mul _ hb, ← colD_inv, levi_mul TR (good_inv X (good_colD hP1)) (good_colD hP2),
        levi_inv TR (good_colD hP1)]
      rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, heq, mul_assoc, mul_inv_cancel, mul_one]
    have hmU : ∀ v, Formalism.L2.SG.GGMirabolic.IsUni D.R.k
        (levi TR (colD (iotaF X u γ1 * cs.h ρ1.1) (iotaF X u γ2 * cs.h ρ2.1)) v) := by
      rw [hlm]; exact UG_mul TR w1.2 (UG_inv TR w2.2)
    have hm2 := mem_level_of_unitriangular TR (good_colD hmK) (ncong_colDiff u _ _ hmK) hmU
    have hku := colD_ku hK hm2

    have hρ : ρ1.1 = ρ2.1 := by
      have hu := hR (cs.h ρ2.1)
      refine hu.unique ?_ ⟨1, 1, by simp⟩
      refine ⟨γ2⁻¹ * γ1, ⟨_, hku⟩, ?_⟩
      simp only [map_mul, map_inv]
      group
    have hρ' : ρ1 = ρ2 := Subtype.ext hρ
    subst hρ'

    have hγ : γ1 = γ2 := by
      have h0 : γ1⁻¹ * γ2 = 1 := by
        refine hN (cs.h ρ1.1) (γ1⁻¹ * γ2) ?_
        have e : (cs.h ρ1.1)⁻¹ * iotaF X u (γ1⁻¹ * γ2) * cs.h ρ1.1 =
            (iotaF X u γ1 * cs.h ρ1.1)⁻¹ * (iotaF X u γ2 * cs.h ρ1.1) := by
          simp only [map_mul, map_inv]; group
        rw [e]; exact hku
      rw [inv_mul_eq_one] at h0; exact h0
    subst hγ
    have ha : a1 = a2 := ha1e.trans ha2e.symm
    subst ha
    have hw : (w1 : Iof TR) = w2 := mul_left_cancel heq
    have : w1 = w2 := Subtype.ext hw
    subst this
    rfl
  · intro s
    obtain ⟨h, hk, hki, hs⟩ := hO q s
    obtain ⟨ρ, ⟨γ, κ, hh⟩, -⟩ := hR h
    have hlam : cs.lamOf ρ = q.1 := hRep q h ρ γ κ hk hh
    have hκ2 : colD 1 (κ : Hfin X u) ∈ X.K2 := by
      have := κ.2
      have e : colD 1 (κ : Hfin X u) = (X.xu u)⁻¹ * ((κ : Hfin X u) : X.B.I.Gf) * X.xu u := by
        unfold colD; simp only [Subgroup.coe_one, one_mul]; group
      rw [e]; exact this
    have hκK : colD 1 (κ : Hfin X u) ∈ X.B.I.Kset := hκ2.1
    have haE : colD hb (iotaF X u γ * hb) = colD hb h * (colD 1 (κ : Hfin X u))⁻¹ * colD (cs.h ρ) hb := by
      rw [hh]; unfold colD; simp only [Subgroup.coe_mul, Subgroup.coe_one, one_mul]; group
    have haK : colD hb (iotaF X u γ * hb) ∈ X.B.I.Kset := by
      rw [haE]; exact K_mul X.B.I (K_mul X.B.I hk (K_inv X.B.I hκK)) (kKi ρ hlam)
    have ga := good_colD haK
    have gr := good_colD (kK ρ hlam)
    have gk := good_colD hκK
    refine ⟨⟨⟨levi TR (colD hb (iotaF X u γ * hb)), γ, by rw [aK]; exact haK, by rw [aK]⟩,
      ⟨ρ, Subtype.ext hlam⟩, ⟨levi TR (colD 1 (κ : Hfin X u)), fun v => unitriangular_reduction_of_mem_level TR gk hκ2 v⟩⟩, ?_⟩
    simp only
    rw [show scOf TR cs ρ = levi TR (colD hb (cs.h ρ)) by rw [scOf_eq, hlam], ← levi_mul TR ga gr,
      ← levi_mul TR (good_mul X ga gr) gk, colD_conj]
    have e2 : colD hb (iotaF X u γ * cs.h ρ) * colD 1 (κ : Hfin X u) = colD hb h := by
      rw [hh]; unfold colD; simp only [Subgroup.coe_mul, Subgroup.coe_one, one_mul]; group
    rw [e2, hs]

end ColFreeBij

end Formalism.L2.SG.NormCut
end
end

section

noncomputable section

open Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting
open scoped Classical TensorProduct

namespace Formalism.L2.SG.Pf.SlabNDensePf

open Formalism.L2.SG Formalism.L2.SG.PoincareInHH Formalism.L2.SG.Pf.Unip Formalism.L2.SG.Pf.UnipB

section Defs

variable {D : D7} (X : HidaSetting D)

abbrev RA : Type := X.B.I.E ⊗[X.B.I.F] Af X.B.I.F

abbrev ic : X.B.I.E →+* RA X := Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F)

instance inv2 : Invertible (2 : RA X) :=
  (Invertible.map (ic X) (2 : X.B.I.E)).copy 2 (map_ofNat (ic X) 2).symm

def Bf : Matrix (Fin X.B.I.n) (Kap X) (RA X) := (Bm X).map (ic X)
def Bf' : Matrix (Kap X) (Fin X.B.I.n) (RA X) := (Bm' X).map (ic X)
def JBf : Matrix (Kap X) (Kap X) (RA X) := (JB X).map (ic X)

def Mf (x : X.B.I.Gf) : Matrix (Kap X) (Kap X) (RA X) := Bf' X * X.B.I.fmat x * Bf X

def Cg {α β : Type*} (c : ℕ) (A : Matrix α β (RA X)) : Prop :=
  ∀ i j, ∃ t ∈ IntAf X.B.I.F X.B.I.E, A i j = (c : RA X) * t

end Defs

def NfPat : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (x : X.B.I.Gf), x ∈ X.NfinU u → InPat (lvk X) 1 (Mf X x - 1)

def NfOfPat : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (x : X.B.I.Gf), InPat (lvk X) 1 (Mf X x - 1) → x ∈ X.NfinU u

def CayInvR : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (x : X.B.I.Gf), InPat (lvk X) 1 (Mf X x - 1) →
    ∃ Z : Matrix (Kap X) (Kap X) (RA X), InPat (lvk X) 1 Z ∧
      Formalism.UG.cT (Formalism.UG.sigR X.B.I.cm.sig (Af X.B.I.F)) Z * JBf X = -(JBf X * Z) ∧ cay (2 * D.R.rS + 2) Z = Mf X x

def SkewApprox : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (Z : Matrix (Kap X) (Kap X) (RA X)), InPat (lvk X) 1 Z →
    Formalism.UG.cT (Formalism.UG.sigR X.B.I.cm.sig (Af X.B.I.F)) Z * JBf X = -(JBf X * Z) → ∀ c : ℕ, 1 ≤ c →
      ∃ Y : Matrix (Kap X) (Kap X) X.B.I.E, InPat (lvk X) 1 Y ∧ Yᴴ * JB X = -(JB X * Y) ∧
        Cg X c (Y.map (ic X) - Z)

def CayCont : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (Z : Matrix (Kap X) (Kap X) (RA X)) (c : ℕ), 1 ≤ c →
    ∃ c' : ℕ, 1 ≤ c' ∧ ∀ Z' : Matrix (Kap X) (Kap X) (RA X), Cg X c' (Z' - Z) →
      Cg X c (cay (2 * D.R.rS + 2) Z' - cay (2 * D.R.rS + 2) Z)

def KgOfClose : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (x : X.B.I.Gf) (g : ℕ), 1 ≤ g →
    ∃ c : ℕ, 1 ≤ c ∧ ∀ y : X.B.I.Gf, Cg X c (Mf X y - Mf X x) → x⁻¹ * y ∈ X.B.I.Kg g

end Formalism.L2.SG.Pf.SlabNDensePf
end
end
