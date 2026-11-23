module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.HaarSubS
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.NGClosed
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SynthesizedVectorZPairing
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle043
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle032
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InHHDef
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.SCompact
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

@[expose] public section

section

noncomputable section

open Matrix
open scoped ComplexConjugate

namespace Formalism.L2.S.Pv.SecW

open Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj.InfCut Formalism.L2.SG.RealObj.InfCut.NilradicalHermitianFrames.NH

variable {n r k : ℕ} (ε : Fin n → Bool)

def fr2L (e p : Fin r → Fin n → ℂ) (z : Fin n → ℂ) (w : Fin k → Fin n → ℂ)
    (e' p' : Fin r → Fin n → ℂ) (z' : Fin n → ℂ) (w' : Fin k → Fin n → ℂ) (T : ℝ) :
    (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ) where
  toFun v := syn e' p' z' w' T (fun a => hJ ε (p a) v) (fun a => hJ ε (e a) v) (hJ ε z v) (fun j => hJ ε (w j) v)
  map_add' v v' := by
    simp only [syn, UnitaryIsometries.hJ_add_right, add_smul, Finset.sum_add_distrib, neg_add, add_div]
    abel
  map_smul' c v := by
    simp only [syn, UnitaryIsometries.hJ_smul_right, RingHom.id_apply, smul_add, Finset.smul_sum, smul_smul]
    rw [show -(c * hJ ε z v) / (T : ℂ) = c * (-hJ ε z v / T) by ring]

def fr2M (e p : Fin r → Fin n → ℂ) (z : Fin n → ℂ) (w : Fin k → Fin n → ℂ)
    (e' p' : Fin r → Fin n → ℂ) (z' : Fin n → ℂ) (w' : Fin k → Fin n → ℂ) (T : ℝ) : Matrix (Fin n) (Fin n) ℂ :=
  LinearMap.toMatrix' (fr2L ε e p z w e' p' z' w' T)

variable {ε} {e p : Fin r → Fin n → ℂ} {z : Fin n → ℂ} {w : Fin k → Fin n → ℂ}
  {e' p' : Fin r → Fin n → ℂ} {z' : Fin n → ℂ} {w' : Fin k → Fin n → ℂ} {T : ℝ}

theorem frameChangeMatrix_mulVec (v : Fin n → ℂ) :
    fr2M ε e p z w e' p' z' w' T *ᵥ v =
      syn e' p' z' w' T (fun a => hJ ε (p a) v) (fun a => hJ ε (e a) v) (hJ ε z v) (fun j => hJ ε (w j) v) := by
  unfold fr2M
  rw [LinearMap.toMatrix'_mulVec]
  rfl

theorem frameChangeMatrix_entry (i j : Fin n) :
    fr2M ε e p z w e' p' z' w' T i j =
      syn e' p' z' w' T (fun a => hJ ε (p a) (Pi.single j 1)) (fun a => hJ ε (e a) (Pi.single j 1))
        (hJ ε z (Pi.single j 1)) (fun l => hJ ε (w l) (Pi.single j 1)) i := by
  have h : fr2M ε e p z w e' p' z' w' T *ᵥ Pi.single j 1 = _ := frameChangeMatrix_mulVec _
  rw [Matrix.mulVec_single_one] at h
  exact congrFun h i

theorem frameChangeMatrix_isometry (F : Frm ε e p z w T) (F' : Frm ε e' p' z' w' T) (hdim : n = 2 * r + 1 + k) :
    UnitaryIsometries.IsIsom ε (fr2M ε e p z w e' p' z' w' T) := by
  intro x y
  rw [frameChangeMatrix_mulVec, frameChangeMatrix_mulVec, hJ_syn_syn F']
  conv_rhs => rw [recon F hdim x, recon F hdim y, hJ_syn_syn F]

theorem frameChangeMatrix_isotropic (F : Frm ε e p z w T) (b : Fin r) : fr2M ε e p z w e' p' z' w' T *ᵥ e b = e' b := by
  rw [frameChangeMatrix_mulVec]
  have h1 : (fun a => hJ ε (p a) (e b)) = fun a => if a = b then (1 : ℂ) else 0 := by
    funext a
    rw [UnitaryIsometries.hJ_conj, F.ep b a]
    by_cases hab : a = b
    · subst hab
      simp
    · simp [hab, Ne.symm hab]
  have h2 : (fun a => hJ ε (e a) (e b)) = fun _ => (0 : ℂ) := by
    funext a
    exact F.ee a b
  have h3 : hJ ε z (e b) = 0 := by rw [UnitaryIsometries.hJ_conj, F.ez b, map_zero]
  have h4 : (fun j => hJ ε (w j) (e b)) = fun _ => (0 : ℂ) := by
    funext j
    rw [UnitaryIsometries.hJ_conj, F.ew b j, map_zero]
  rw [h1, h2, h3, h4]
  simp [syn]

theorem fr2M_mulVec_z (F : Frm ε e p z w T) : fr2M ε e p z w e' p' z' w' T *ᵥ z = z' := by
  rw [frameChangeMatrix_mulVec]
  have h1 : (fun a => hJ ε (p a) z) = fun _ => (0 : ℂ) := by
    funext a
    exact F.pz a
  have h2 : (fun a => hJ ε (e a) z) = fun _ => (0 : ℂ) := by
    funext a
    exact F.ez a
  have h4 : (fun j => hJ ε (w j) z) = fun _ => (0 : ℂ) := by
    funext j
    rw [UnitaryIsometries.hJ_conj, F.zw j, map_zero]
  rw [h1, h2, F.zz, h4]
  have hT : (T : ℂ) ≠ 0 := by exact_mod_cast F.T_ne
  simp [syn, hT]

end Formalism.L2.S.Pv.SecW
end
end

section

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Matrix

namespace Formalism.L2.S.Pv.HaarSubS

open Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.L2.SG.RealObj.InfCut Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem frm_at {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u : D.what₂.Word) (v : InfinitePlace X.B.I.F) :
    ∃ w : Fin D.R.k → Fin X.B.I.n → ℂ, NilradicalHermitianFrames.NH.Frm (X.B.I.ε v) (fun a => rv X.B.I v (X.eR a))
      (fun a => rv X.B.I v (X.fR a)) (rv X.B.I v (X.zR u)) w (Tw u) := by
  have hdim : X.B.I.n = 2 * D.R.rS + 1 + D.R.k := (Formalism.L2.SG.Pf.card_frame X).symm
  have hsig := Formalism.L2.SG.PoincareInHH.Cut.card_eps_false X v
  have hpos : 0 < Tw u := by
    unfold Tw
    exact_mod_cast (D.mem u).A.T_prime.pos
  have hee : ∀ a b, hJ (X.B.I.ε v) (rv X.B.I v (X.eR a)) (rv X.B.I v (X.eR b)) = 0 :=
    fun a b => (Formalism.L2.SG.PoincareInHH.Cut.hJ_crd X v _ _).trans (by rw [X.ee]; simp)
  have hez : ∀ a, hJ (X.B.I.ε v) (rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u)) = 0 :=
    fun a => (Formalism.L2.SG.PoincareInHH.Cut.hJ_crd X v _ _).trans (by rw [(X.zu_orth u a).1]; simp)
  have hzz : hJ (X.B.I.ε v) (rv X.B.I v (X.zR u)) (rv X.B.I v (X.zR u)) = -(Tw u : ℂ) :=
    (Formalism.L2.SG.PoincareInHH.Cut.hJ_crd X v _ _).trans (by rw [X.zu_norm u]; simp [Tw])
  have hep : ∀ a b, hJ (X.B.I.ε v) (rv X.B.I v (X.eR a)) (rv X.B.I v (X.fR b)) = if a = b then 1 else 0 :=
    fun a b => (Formalism.L2.SG.PoincareInHH.Cut.hJ_crd X v _ _).trans (by rw [X.ef]; split_ifs <;> simp)
  have hpp : ∀ a b, hJ (X.B.I.ε v) (rv X.B.I v (X.fR a)) (rv X.B.I v (X.fR b)) = 0 := fun a b =>
    (Formalism.L2.SG.PoincareInHH.Cut.hJ_crd X v _ _).trans (by rw [X.ff]; simp)
  have hpz : ∀ a, hJ (X.B.I.ε v) (rv X.B.I v (X.fR a)) (rv X.B.I v (X.zR u)) = 0 := fun a =>
    (Formalism.L2.SG.PoincareInHH.Cut.hJ_crd X v _ _).trans (by rw [(X.zu_orth u a).2]; simp)
  obtain ⟨w, hww, hew, hpw, hzw⟩ := UnitaryIsometries.RI.complement (X.B.I.ε v) hdim hsig hpos
    (⟨hee, hep, hpp, hez, hpz, hzz⟩ : UnitaryIsometries.RI.Hyp (X.B.I.ε v) _ _ _ _)
  exact ⟨w, ⟨hee, hep, hpp, hez, hpz, hzz, hew, hpw, hzw, hww, hpos.ne'⟩⟩

theorem mem_Hu_iff {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u : D.what₂.Word) (s : X.B.I.Ginf) :
    s ∈ Hu X u ↔ ∀ v, s v ∈ NilradicalHermitianFrames.NH.HG (X.B.I.ε v) (fun a => rv X.B.I v (X.eR a))
      (fun a => rv X.B.I v (X.fR a)) (rv X.B.I v (X.zR u)) := by
  constructor
  · intro hs v
    refine ⟨fun a => hs v _ ?_, fun a => hs v _ ?_, hs v _ ?_⟩
    · exact Or.inl (Or.inl ⟨a, rfl⟩)
    · exact Or.inl (Or.inr ⟨a, rfl⟩)
    · exact Or.inr rfl
  · intro hs v x hx
    rcases hx with (⟨a, rfl⟩ | ⟨a, rfl⟩) | hx
    · exact (hs v).1 a
    · exact (hs v).2.1 a
    · rw [Set.mem_singleton_iff] at hx
      subst hx
      exact (hs v).2.2

theorem Hu_eq_pi {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u : D.what₂.Word) : Hu X u = Set.pi Set.univ (fun v => (NilradicalHermitianFrames.NH.HG (X.B.I.ε v) (fun a => rv X.B.I v (X.eR a))
    (fun a => rv X.B.I v (X.fR a)) (rv X.B.I v (X.zR u)) : Set (Formalism.REAL.UJ (X.B.I.ε v)))) := by
  ext s
  rw [mem_Hu_iff]
  simp

theorem sDecomp_holds : SDecomp := by
  intro D X u
  have hw := fun v => frm_at X u v
  choose w Fw using hw
  have hdim : ∀ v : InfinitePlace X.B.I.F, X.B.I.n = 2 * D.R.rS + 1 + D.R.k := fun _ => (Formalism.L2.SG.Pf.card_frame X).symm
  set SGv := fun v => UnitaryIsometries.RI.SG (X.B.I.ε v) (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u)) with hSGv
  set NGv := fun v => NilradicalHermitianFrames.NH.NG (X.B.I.ε v) (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u)) with hNGv
  set HGv := fun v => NilradicalHermitianFrames.NH.HG (X.B.I.ε v) (fun a => rv X.B.I v (X.eR a)) (fun a => rv X.B.I v (X.fR a))
    (rv X.B.I v (X.zR u)) with hHGv
  have hS : ∀ s, s ∈ X.SinfU u ↔ ∀ v, s v ∈ SGv v := fun s => Iff.rfl
  have hN : ∀ s, s ∈ X.NinfU u ↔ ∀ v, s v ∈ NGv v := fun s => Iff.rfl
  have hH : ∀ s, s ∈ Hu X u ↔ ∀ v, s v ∈ HGv v := mem_Hu_iff X u
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have he : X.SinfU u = ⋂ v, (fun s : X.B.I.Ginf => s v) ⁻¹' (SGv v : Set _) := by
      ext s
      simp only [Set.mem_iInter, Set.mem_preimage, SetLike.mem_coe]
      exact hS s
    rw [he]
    exact isClosed_iInter fun v => (UnitaryIsometries.RI.SG_closed _ _ _).preimage (continuous_apply v)
  · exact (hS 1).2 fun v => (SGv v).one_mem
  · intro a ha b hb
    exact (hS _).2 fun v => (SGv v).mul_mem ((hS a).1 ha v) ((hS b).1 hb v)
  · intro a ha
    exact (hS _).2 fun v => (SGv v).inv_mem ((hS a).1 ha v)
  · exact (hN 1).2 fun v => (NGv v).one_mem
  · intro a ha b hb
    exact (hN _).2 fun v => (NGv v).mul_mem ((hN a).1 ha v) ((hN b).1 hb v)
  · intro a ha
    exact (hN _).2 fun v => (NGv v).inv_mem ((hN a).1 ha v)
  · rw [Hu_eq_pi]
    exact isCompact_univ_pi fun v => NilradicalHermitianFrames.NH.HG_compact (Fw v) (hdim v)
  · exact (hH 1).2 fun v => (HGv v).one_mem
  · intro a ha b hb
    exact (hH _).2 fun v => (HGv v).mul_mem ((hH a).1 ha v) ((hH b).1 hb v)
  · intro a ha
    exact (hH _).2 fun v => (HGv v).inv_mem ((hH a).1 ha v)
  · intro h hh n hn
    exact (hN _).2 fun v => NilradicalHermitianFrames.NH.conj_mem _ _ _ _ ((hH h).1 hh v) ((hN n).1 hn v)
  · intro n hn h hh
    exact (hS _).2 fun v => (SGv v).mul_mem (NilradicalHermitianFrames.NH.NG_le_SG _ _ _ ((hN n).1 hn v))
      (NilradicalHermitianFrames.NH.HG_le_SG _ _ _ _ ((hH h).1 hh v))
  · intro s hs
    have hdec := fun v => NilradicalHermitianFrames.NH.mem_NH (Fw v) (hdim v) ((hS s).1 hs v)
    choose m hm h hh heq using hdec
    exact ⟨m, (hN m).2 hm, h, (hH h).2 hh, funext heq⟩

end Formalism.L2.S.Pv.HaarSubS
end
end
