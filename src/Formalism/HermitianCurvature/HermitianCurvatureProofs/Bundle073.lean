module

public import Formalism.HermitianCurvature.Bundle004
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.PhiBoundPartsOfRadicalParametrisation
public import Formalism.HermitianCurvature.Bundle009
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle065
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.OperatorRepresentations
public import Formalism.HermitianCurvature.FiniteOrderIntersectionInSmooth
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.FlagSpanVanishing
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle038
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.InverseSplitting
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LowerParabolicCoordinates
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle054
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle070
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle052
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Lemma
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

@[expose] public section

section

open Matrix MeasureTheory Filter Topology
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.CellSmoothness

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

lemma contDiffOn_gq (D : RealPlaceData k r Wp Wq) : ContDiffOn ℝ ∞ (fun q => gq D q) (QDom k r D.z D.z') := by
  refine Formalism.FourierDecayAlt.P.Ux10.cdm_iff.2 fun i j => ?_
  simp only [gq, bigCell]
  split_ifs with h1 h2 h3 h4 h5
  · exact ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin r => ℂ) (⟨j.val, h1⟩ : Fin r)).comp
      (ContinuousLinearMap.fst ℝ (Fin r → ℂ) ℂ)).contDiff.contDiffOn
  · exact contDiffOn_const
  · exact (D.sec.1 _ _).comp contDiff_snd.contDiffOn (fun q hq => hq.2)
  · exact contDiffOn_const
  · refine ContDiffOn.inv ?_ ?_
    · exact (Complex.conjCLE.contDiff.comp ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin r => ℂ)
        (⟨2 * r + k - j.val, by omega⟩ : Fin r)).comp (ContinuousLinearMap.fst ℝ (Fin r → ℂ) ℂ)).contDiff).contDiffOn
    · intro q hq
      simpa using hq.1 _
  · exact contDiffOn_const

end Formalism.FourierDecayAlt.P.CellSmoothness
end
end

section

open Finset

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.KLExA

open Formalism.REAL Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Qr

section Int

variable {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']

theorem ofFn_prod_int {t : ℕ} (F : Fin t → Module.End ℂ V) (F' : Fin t → Module.End ℂ V') (f : V →ₗ[ℂ] V')
    (h : ∀ k x, f (F k x) = F' k (f x)) (x : V) : f ((List.ofFn F).prod x) = (List.ofFn F').prod (f x) := by
  induction t generalizing x with
  | zero => simp
  | succ t ih =>
    rw [List.ofFn_succ, List.ofFn_succ, List.prod_cons, List.prod_cons, Module.End.mul_apply, Module.End.mul_apply,
      h, ih (fun k => F k.succ) (fun k => F' k.succ) (fun k y => h k.succ y)]

theorem tm_int {n : ℕ} {E : Fin n → Fin n → Module.End ℂ V} {E' : Fin n → Fin n → Module.End ℂ V'} (f : V →ₗ[ℂ] V')
    (hf : ∀ a b x, f (E a b x) = E' a b (f x)) (u : ℂ) (a b : Fin n) (x : V) :
    f (Tm E u a b x) = Tm E' u a b (f x) := by
  unfold Tm
  split_ifs <;> simp [Module.algebraMap_end_apply, hf]

theorem qminor_int {n t : ℕ} {E : Fin n → Fin n → Module.End ℂ V} {E' : Fin n → Fin n → Module.End ℂ V'}
    (f : V →ₗ[ℂ] V') (hf : ∀ a b x, f (E a b x) = E' a b (f x)) (a b : Fin t → Fin n) (u : ℂ) (x : V) :
    f (qminor E a b u x) = qminor E' a b u (f x) := by
  unfold qminor

  rw [LinearMap.sum_apply, LinearMap.sum_apply, map_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Module.End.mul_apply, Module.End.mul_apply, Module.End.intCast_apply, Module.End.intCast_apply, map_zsmul,
    ofFn_prod_int _ _ f (fun k y => tm_int f hf _ _ _ y)]

theorem qdet_int {n : ℕ} {E : Fin n → Fin n → Module.End ℂ V} {E' : Fin n → Fin n → Module.End ℂ V'}
    (f : V →ₗ[ℂ] V') (hf : ∀ a b x, f (E a b x) = E' a b (f x)) (u : ℂ) (x : V) :
    f (qdet E u x) = qdet E' u (f x) :=
  qminor_int f hf id id u x

end Int

section Restr

variable {V : Type} [AddCommGroup V] [Module ℂ V] {n : ℕ}

def resE (E : Fin n → Fin n → Module.End ℂ V) (S : Submodule ℂ V) (hS : Stab E S) : Fin n → Fin n → Module.End ℂ S :=
  fun a b => (E a b).restrict (hS a b)

theorem resE_apply (E : Fin n → Fin n → Module.End ℂ V) (S : Submodule ℂ V) (hS : Stab E S) (a b : Fin n) (x : S) :
    ((resE E S hS a b x : S) : V) = E a b x := rfl

theorem glRel_resE {E : Fin n → Fin n → Module.End ℂ V} (hE : GlRel E) (S : Submodule ℂ V) (hS : Stab E S) :
    GlRel (resE E S hS) := by
  intro a b c d
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  have h := LinearMap.congr_fun (hE a b c d) (x : V)
  by_cases hbc : b = c <;> by_cases hda : d = a <;>
    simp only [hbc, hda, if_true, if_false, Module.End.mul_apply, LinearMap.sub_apply, LinearMap.zero_apply,
      Submodule.coe_sub, Submodule.coe_zero, sub_zero, zero_sub, resE_apply] at h ⊢ <;> exact h

theorem irr_resE {E : Fin n → Fin n → Module.End ℂ V} (S : Submodule ℂ V) (hS : Stab E S) (hne : S ≠ ⊥)
    (hirr : ∀ S' : Submodule ℂ V, S' ≤ S → Stab E S' → S' = ⊥ ∨ S' = S) : Irr (resE E S hS) := by
  refine ⟨Submodule.nontrivial_iff_ne_bot.2 hne, fun T hT => ?_⟩
  have hinj := Submodule.map_injective_of_injective S.injective_subtype
  have hst : Stab E (T.map S.subtype) := by
    intro a b v hv
    obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.1 hv
    exact Submodule.mem_map.2 ⟨resE E S hS a b x, hT a b x hx, rfl⟩
  rcases hirr (T.map S.subtype) (Submodule.map_subtype_le S T) hst with h | h
  · left
    exact hinj (h.trans (Submodule.map_bot _).symm)
  · right
    exact hinj (h.trans (Submodule.map_subtype_top S).symm)

theorem cap_resE {E : Fin n → Fin n → Module.End ℂ V} (m : Fin n → ℂ) (hS : Stab E (CapSp E m)) (w : ℂ)
    (x : CapSp E m) : qdet (resE E (CapSp E m) hS) w x = cpol m w • x := by
  apply Subtype.ext
  rw [Submodule.coe_smul]
  have := qdet_int (CapSp E m).subtype (E := resE E (CapSp E m) hS) (E' := E) (fun a b y => rfl) w x
  simp only [Submodule.subtype_apply] at this
  rw [this]
  exact mem_CapSp.1 x.2 w

end Restr

section Proj

variable {V : Type} [AddCommGroup V] [Module ℂ V] {ι : Type} [Fintype ι] [DecidableEq ι] {S : ι → Submodule ℂ V}

def projI (h : DirectSum.IsInternal S) (i : ι) : V →ₗ[ℂ] S i :=
  (DirectSum.component ℂ ι (fun j => S j) i).comp (LinearEquiv.ofBijective (DirectSum.coeLinearMap S) h).symm.toLinearMap

theorem projI_apply (h : DirectSum.IsInternal S) (i : ι) (v : V) :
    projI h i v = (LinearEquiv.ofBijective (DirectSum.coeLinearMap S) h).symm v i := rfl

theorem projI_self (h : DirectSum.IsInternal S) {i : ι} (x : S i) : projI h i (x : V) = x := by
  rw [projI_apply]
  exact DirectSum.IsInternal.ofBijective_coeLinearMap_same h x

theorem projI_ne (h : DirectSum.IsInternal S) {i j : ι} (hij : j ≠ i) (x : S j) : projI h i (x : V) = 0 := by
  rw [projI_apply]
  exact DirectSum.IsInternal.ofBijective_coeLinearMap_of_ne h hij x

theorem projI_sum (h : DirectSum.IsInternal S) (y : ∀ j, S j) (i : ι) : projI h i (∑ j, (y j : V)) = y i := by

  rw [map_sum, Finset.sum_eq_single i (fun j _ hj => projI_ne h hj (y j)) (fun hi => absurd (Finset.mem_univ i) hi)]
  exact projI_self h (y i)

theorem sum_projI (h : DirectSum.IsInternal S) (v : V) : ∑ j, (projI h j v : V) = v := by
  set e := LinearEquiv.ofBijective (DirectSum.coeLinearMap S) h with he
  have h1 : DirectSum.coeLinearMap S (e.symm v) = v := e.apply_symm_apply v
  conv_rhs => rw [← h1, ← DirectSum.sum_univ_of (e.symm v)]

  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [DirectSum.coeLinearMap_of]
  rfl

theorem projI_comm (h : DirectSum.IsInternal S) (T : Module.End ℂ V) (hT : ∀ j, ∀ v ∈ S j, T v ∈ S j) (i : ι) (v : V) :
    projI h i (T v) = T.restrict (hT i) (projI h i v) := by
  have e : T v = ∑ j, ((T.restrict (hT j) (projI h j v) : S j) : V) := by
    conv_lhs => rw [← sum_projI h v]

    rw [map_sum]
    rfl
  rw [e, projI_sum]

end Proj

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.KLExA
end
end

section

open Matrix Finset

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR.TW

open Formalism.REAL Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr

def TWNeAlg : Prop :=
  ∀ (V V' : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] [AddCommGroup V'] [Module ℂ V']
    [FiniteDimensional ℂ V'] (n : ℕ) (E : Fin (n + 1) → Fin (n + 1) → Module.End ℂ V)
    (E' : Fin (n + 1) → Fin (n + 1) → Module.End ℂ V') (β β' : ℂ) (L L' : Fin (n + 1) → ℤ) (M M' : Fin n → ℤ) (i : Fin n),
    Hyp E β L → Hyp E' β' L' → Box L M → Box L' M' → Box L (Function.update M i (M i + 1)) →
    Box L' (Function.update M' i (M' i + 1)) → shf β M = shf β' M' →
    ∀ J : V' →ₗ[ℂ] V, J ≠ 0 → (∀ a b v, J (subA E' a b v) = subA E a b (J v)) →
    (∀ v, J v ∈ CapSp (subA E) (shf β M)) →
    ∃ v' : V', (∑ c, etaK E c (J (yK E' c v'))) ≠ 0 ∧
      (∑ c, etaK E c (J (yK E' c v'))) ∈ CapSp (subA E) (shf β (Function.update M i (M i + 1)))

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR.TW
end
end

section

open Matrix Finset
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace AnisotropicColumnSums

theorem chat_gen (t n : ℕ) (h : t = n + 1) (A : Type) [Ring A] [Algebra ℂ A] (Eop : Fin t → Fin t → A)
    (P Q : Matrix (Fin t) (Fin t) ℂ) (la : Fin t) (hla : la.val = n) (ι : Fin n → Fin t)
    (hι : ∀ a, (ι a).val = a.val) (hE : GlRel Eop) (hQP : Q * P = 1) (hPQ : P * Q = 1) (u : ℂ) (β : Fin t → ℂ)
    (hβ : ∀ j, j ≠ la → (β ᵥ* P) j = 0) :
    chatA Eop u (fun p => P p la) β = (β ᵥ* P) la • qminor (Econj Eop P Q) ι ι u := by
  subst h
  have e1 : la = Fin.last n := Fin.ext hla
  subst e1
  have e2 : ι = skip1 (Fin.last n) := by
    funext a
    apply Fin.ext
    have := a.isLt
    simp [skip1, hι]
  rw [e2]
  exact first_contraction_adapted A n Eop P Q hE hQP hPQ u β hβ

variable {k r : ℕ}

theorem sum_last {v : Fin (2 * r + k + 1) → ℂ} (hv : inWb k r v) (w : Fin (2 * r + k + 1) → ℂ) :
    ∑ d, herm (Hpk k r) (bvec (posL k r (Fin.last r) d)) w * v (posL k r (Fin.last r) d) = herm (Hpk k r) v w := by
  have hinj : ∀ c c' : Fin (mdim k r (Fin.last r)), posL k r (Fin.last r) c = posL k r (Fin.last r) c' → c = c' := by
    intro c c' h
    ext
    simp only [posL, Fin.ext_iff] at h
    omega
  have hsurj : ∀ p, Qx2.inV k r (Fin.last r) p → ∃ c, posL k r (Fin.last r) c = p := by
    intro p hp
    simp only [Qx2.inV, Fin.val_last] at hp
    refine ⟨⟨p.val - r, ?_⟩, ?_⟩
    · simp only [mdim, Fin.val_last]
      omega
    · ext
      simp only [posL, Fin.val_last]
      omega
  have hv' : v = ∑ d, v (posL k r (Fin.last r) d) • bvec (posL k r (Fin.last r) d) := by
    ext q
    simp only [Finset.sum_apply, Pi.smul_apply, bvec, Pi.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
    by_cases hq : Qx2.inV k r (Fin.last r) q
    · obtain ⟨d0, rfl⟩ := hsurj q hq
      rw [Fintype.sum_eq_single d0]
      · simp
      · intro d hd
        have hne : posL k r (Fin.last r) d0 ≠ posL k r (Fin.last r) d := fun h => hd (hinj _ _ h).symm
        simp [hne]
    · rw [Finset.sum_eq_zero]
      · apply hv
        simp only [Qx2.inV, Fin.val_last] at hq
        omega
      · intro d _
        have hne : q ≠ posL k r (Fin.last r) d := by
          rintro rfl
          apply hq
          have hd := d.isLt
          simp only [Qx2.inV, posL, mdim, Fin.val_last] at hd ⊢
          omega
        simp [hne]
  conv_rhs => rw [hv']
  unfold herm
  rw [Matrix.mulVec_sum, dotProduct_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]
  ring

def bcol (k r : ℕ) (x : Fin (2 * r + k + 1) → ℂ) (Bs : Fin k → Fin (2 * r + k + 1) → ℂ)
    (j : Fin (mdim k r (Fin.last r))) : Fin (2 * r + k + 1) → ℂ :=
  if h : j.val < k then Bs ⟨j.val, h⟩ else x

def nrm (k r : ℕ) (x : Fin (2 * r + k + 1) → ℂ) (j : Fin (mdim k r (Fin.last r))) : ℂ :=
  if j.val < k then 1 else (herm (Hpk k r) x x)⁻¹

theorem mdim_last : mdim k r (Fin.last r) = k + 1 := by
  simp [mdim]

theorem bcol_inWb {x : Fin (2 * r + k + 1) → ℂ} {Bs : Fin k → Fin (2 * r + k + 1) → ℂ} (hx : inWb k r x)
    (hB : IsFrameOf k r [x] Bs) (j : Fin (mdim k r (Fin.last r))) : inWb k r (bcol k r x Bs j) := by
  unfold bcol
  split_ifs
  · exact hB.1 _
  · exact hx

theorem herm_bcol_eq_ite {x : Fin (2 * r + k + 1) → ℂ} {Bs : Fin k → Fin (2 * r + k + 1) → ℂ}
    (hB : IsFrameOf k r [x] Bs) (j : Fin (mdim k r (Fin.last r))) :
    herm (Hpk k r) (bcol k r x Bs j) x = if j.val < k then 0 else herm (Hpk k r) x x := by
  unfold bcol
  by_cases h : j.val < k
  · rw [dite_eq_left h, if_pos h]
    exact hB.2.2 _ x (List.mem_singleton_self x)
  · rw [dite_eq_right h, if_neg h]

private theorem herm_eq_star_herm_swap (v w : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) v w = star (herm (Hpk k r) w v) := by
  unfold herm
  rw [Matrix.star_dotProduct, Matrix.star_mulVec, Qx2.hpk_h, ← Matrix.dotProduct_mulVec]

theorem gram {x : Fin (2 * r + k + 1) → ℂ} {Bs : Fin k → Fin (2 * r + k + 1) → ℂ}
    (hxx : herm (Hpk k r) x x ≠ 0) (hB : IsFrameOf k r [x] Bs) (j j' : Fin (mdim k r (Fin.last r))) :
    herm (Hpk k r) (bcol k r x Bs j') (bcol k r x Bs j) * nrm k r x j = if j = j' then 1 else 0 := by
  obtain ⟨hBw, hBo, hBx⟩ := hB
  have hx0 : ∀ a, herm (Hpk k r) (Bs a) x = 0 := fun a => hBx a x (List.mem_singleton_self x)
  have hx0' : ∀ a, herm (Hpk k r) x (Bs a) = 0 := fun a => by rw [herm_eq_star_herm_swap, hx0, star_zero]
  have hj : j.val < k + 1 := by
    have := j.isLt
    simp only [mdim, Fin.val_last] at this
    omega
  have hj' : j'.val < k + 1 := by
    have := j'.isLt
    simp only [mdim, Fin.val_last] at this
    omega
  unfold bcol nrm
  by_cases h1 : j.val < k <;> by_cases h2 : j'.val < k
  · rw [dite_eq_left h2, dite_eq_left h1, if_pos h1, mul_one, hBo]
    by_cases hjj : j = j'
    · subst hjj
      simp
    · have hne : ¬ j'.val = j.val := fun h => hjj (Fin.ext h.symm)
      simp [hjj, hne]
  · rw [dite_eq_right h2, dite_eq_left h1, if_pos h1, mul_one, hx0', if_neg]
    rintro rfl
    exact h2 h1
  · rw [dite_eq_left h2, dite_eq_right h1, if_neg h1, hx0, zero_mul, if_neg]
    rintro rfl
    exact h1 h2
  · have hjj : j = j' := by
      ext
      omega
    rw [dite_eq_right h2, dite_eq_right h1, if_neg h1, if_pos hjj, mul_inv_cancel₀ hxx]

end AnisotropicColumnSums

open AnisotropicColumnSums in
theorem qr_chatFrame_of : Formalism.FourierDecayAlt.Qr.FrameMinor → Formalism.FourierDecayAlt.Qr.ChatFrame := by
  intro hFM E _ _ k r D hD x Bs hx hxx hB u φ g hg
  set P : Matrix (Fin (mdim k r (Fin.last r))) (Fin (mdim k r (Fin.last r))) ℂ :=
    Matrix.of fun c j => bcol k r x Bs j (posL k r (Fin.last r) c) with hP
  set Q : Matrix (Fin (mdim k r (Fin.last r))) (Fin (mdim k r (Fin.last r))) ℂ :=
    Matrix.of fun j d => herm (Hpk k r) (bvec (posL k r (Fin.last r) d)) (bcol k r x Bs j) * nrm k r x j with hQ
  have hQP : Q * P = 1 := by
    ext j j'
    rw [Matrix.mul_apply, Matrix.one_apply, ← gram hxx hB j j', ← sum_last (bcol_inWb hx hB j'), Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro d _
    simp only [hP, hQ, Matrix.of_apply]
    ring
  have hPQ : P * Q = 1 := mul_eq_one_comm.1 hQP
  let la : Fin (mdim k r (Fin.last r)) := ⟨k, by rw [mdim_last]; omega⟩
  let ι : Fin k → Fin (mdim k r (Fin.last r)) := fun a => ⟨a.val, by rw [mdim_last]; omega⟩
  have hβP : ∀ j, ((fun j => herm (Hpk k r) (bvec (posL k r (Fin.last r) j)) x) ᵥ* P) j =
      if j.val < k then 0 else herm (Hpk k r) x x := by
    intro j
    rw [← herm_bcol_eq_ite hB j, ← sum_last (bcol_inWb hx hB j)]
    rfl
  have hcol : (fun j => x (posL k r (Fin.last r) j)) = fun p => P p la := by
    funext p
    simp [hP, bcol, la]
  have key := chat_gen (mdim k r (Fin.last r)) k mdim_last (Module.End ℂ (SV k r (Fin.last r) D E))
    (EV k r (Fin.last r) D E) P Q la rfl ι (fun _ => rfl) (relation_representation E k r 0 (Fin.last r) D hD).1 hQP hPQ u
    (fun j => herm (Hpk k r) (bvec (posL k r (Fin.last r) j)) x) (by
      intro j hj
      rw [hβP, if_pos]
      have h1 : j.val < k + 1 := lt_of_lt_of_eq j.isLt mdim_last
      have : j.val ≠ k := fun e => hj (Fin.ext e)
      omega)
  rw [hcol, key, hβP, if_neg (by simp [la])]
  have hm := hFM E k r k D hD Bs hB.1 P Q ι (fun a b e => Fin.ext (by have e' := congrArg Fin.val e; exact e'))
    (by
      intro a c
      simp [hP, bcol, ι])
    (by
      intro b d
      simp [hQ, bcol, nrm, ι])
    u φ g hg
  rw [← hm]
  rfl

end Formalism.FourierDecayAlt.P
end
end

section

namespace Formalism.FourierDecayAlt.P

theorem c2_section_decomp : Formalism.FourierDecayAlt.C2.SectionDecomp :=
  c2_section_decomp_of_pieces stabilizer_split stabilizer_pairs unipotent_radical_image upper_splitting standard_flag_property
    unipotent_map_frame zhat_equivalence c2_tau_mem

end Formalism.FourierDecayAlt.P
end
