module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle170
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatQMinOp
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle029
import Formalism.HermitianCurvature.HermitianCurvatureProofs.NormDiagonalEntryDilationGeneratorLeOne
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.OpLEqZeroOfEventually
import Formalism.FormalDegreeBessel.FormalDegreeRatio.BFCell
import Formalism.FormalDegreeBessel.FormalDegreeRatio.GroupFactorizationHolds
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle079
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CompactGroupHaarExists
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.IsCompactZetaLe
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LongWeylElement
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle098
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OppositeWeylSubgroupClosed
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RegularisedPairingViaPhase
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.TheoremPIntegralOfPlaces
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle122
import Formalism.HermitianCurvature.HermitianCurvatureProofs.WeylCellConjTransposeMulApply
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP

open NumberField Matrix

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

noncomputable section

def JDRInvFnM : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (Y : ℂ) (p : B.SS k r), D.inSS p →
    ∀ F : B.Mat k r → (Wq →L[ℂ] Wp), B.CkOn ((r + k : ℕ) : ℕ∞) (B.GV k r) F →
      ∀ g ∈ B.GPos D, rvhatOp k r D.z D.z' Y (B.rho D p F) g = B.rho D p (rvhatOp k r D.z D.z' Y F) g

section poly

open Formalism.FourierDecayAlt.P.PartialDerivativeAlgebra

variable {k r : ℕ}

theorem rim_herm (v w : Fin (2 * r + k + 1) → ℂ) :
    U.IsPolyDeg 1 (fun g : Q.Mx k r => herm (Hpk k r) (g *ᵥ v) w) := by
  have e : (fun g : Q.Mx k r => herm (Hpk k r) (g *ᵥ v) w) =
      fun g => ∑ a, star (w a) * ∑ b, Hpk k r a b * ∑ c, g b c * v c := by
    funext g
    simp only [herm, Matrix.mulVec, dotProduct, Pi.star_apply]
  rw [e]
  exact pd_sum _ fun a _ => ri_mul_left _ (pd_sum _ fun b _ => ri_mul_left _
    (pd_sum _ fun c _ => ri_mul_right (pd_entry b c) _))

theorem rim_rowV (z : Fin (2 * r + k + 1) → ℂ) (J : Fin (r + k) → Fin (2 * r + k + 1)) (p q : Fin (2 * r + k + 1)) :
    U.IsPolyDeg 1 (fun g => rowV k r z g J p q) := by
  unfold rowV
  by_cases h : p.val < r
  · simp only [dif_pos h]
    exact rim_herm _ _
  · by_cases h2 : p.val = r
    · simp only [dif_neg h, dif_pos h2]
      exact rim_herm _ _
    · simp only [dif_neg h, dif_neg h2]
      exact pd_const _ 1

theorem rim_alJ (z : Fin (2 * r + k + 1) → ℂ) (J : Fin (r + k) → Fin (2 * r + k + 1)) :
    U.IsPolyDeg (2 * r + k + 1) (fun g => alJ k r z g J) :=
  pd_det (fun g => Matrix.of fun p q => rowV k r z g J p q) fun a b => by
    simpa only [Matrix.of_apply] using rim_rowV z J a b

end poly

section ops

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

def rimCat {ι : Type} (Θs : ι → B.DiffOp k r Wp Wq) : List ι → B.DiffOp k r Wp Wq
  | [] => []
  | i :: l => Θs i ++ rimCat Θs l

theorem rimCat_poly {ι : Type} {Θs : ι → B.DiffOp k r Wp Wq} {t κ : ℕ} (h : ∀ i, PolyOp t κ (Θs i)) :
    ∀ l, PolyOp t κ (rimCat Θs l)
  | [] => fun T hT => absurd hT List.not_mem_nil
  | i :: l => QMinOp.polyOp_append (h i) (rimCat_poly h l)

theorem rimCat_apply {ι : Type} (Θs : ι → B.DiffOp k r Wp Wq) (F : B.Mat k r → (Wq →L[ℂ] Wp)) (g : B.Mat k r) :
    ∀ l, B.opApply (rimCat Θs l) F g = (l.map fun i => B.opApply (Θs i) F g).sum
  | [] => by simp [rimCat, B.opApply]
  | i :: l => by rw [rimCat, QMinOp.opApply_append, rimCat_apply Θs F g l, List.map_cons, List.sum_cons]

theorem rimCat_order {ι : Type} {Θs : ι → B.DiffOp k r Wp Wq} {t κ : ℕ} (h : ∀ i, PolyOp t κ (Θs i))
    (ho : ∀ i, B.opOrder (Θs i) = t) (i : ι) (l : List ι) :
    B.opOrder (rimCat Θs (i :: l)) = t := by
  rw [rimCat, QMinOp.opOrder_append, ho i]
  exact max_eq_left (ri_order_le _ (rimCat_poly h l))

theorem residue_rows_strict_mono : StrictMono (rowsR k r 0) := by
  intro a b h
  have h' : a.val < b.val := h
  show (rowsR k r 0 a).val < (rowsR k r 0 b).val
  simp only [rowsR]
  split_ifs <;> omega

theorem rim_mem : rowsR k r 0 ∈ jSetR k r := by
  classical
  simp only [jSetR, Finset.mem_filter, Finset.mem_univ, true_and]
  convert (residue_rows_strict_mono (k := k) (r := r))

theorem rim_real (z z' : Fin (2 * r + k + 1) → ℂ) (Y ε : ℂ) :
    ∃ Θ : B.DiffOp k r Wp Wq, PolyOp (r + k) (2 * r + k + 1) Θ ∧ B.opOrder Θ = r + k ∧
      ∀ (UU : Set (B.Mat k r)) (F : B.Mat k r → (Wq →L[ℂ] Wp)), B.CkOn ((r + k : ℕ) : ℕ∞) UU F →
        ∀ g ∈ UU, g ∈ B.GV k r → B.opApply Θ F g = ε • rvhatOp k r z z' Y F g := by
  have h : ∀ x : Fin (k + 1) × (Fin (r + k) → Fin (2 * r + k + 1)),
      ∃ Θ : B.DiffOp k r Wp Wq, PolyOp (r + k) (2 * r + k + 1) Θ ∧ B.opOrder Θ = r + k ∧
      ∀ (UU : Set (B.Mat k r)) (F : B.Mat k r → (Wq →L[ℂ] Wp)), B.CkOn ((r + k : ℕ) : ℕ∞) UU F →
        ∀ g ∈ UU, g ∈ B.GV k r → B.opApply Θ F g = ∑ j ∈ ({()} : Finset Unit),
          (fun (_ : Unit) (g : B.Mat k r) =>
            ε * (((-1 : ℂ) ^ (x.1 : ℕ)) * z' (wI k r x.1) * alJ k r z g x.2)) j g •
            qminorOp (Q.EH k r) x.2 ((fun (_ : Unit) => colsV k r x.1) j) (Q.uC k r (Fin.last r) Y - 1) F g := fun x =>
    QMinOp.qminOpRep {()} x.2 (fun _ => colsV k r x.1) _
      (fun _ _ => ri_mul_left _ (ri_mul_left _ (rim_alJ z x.2))) _
  choose Θs hP hO hR using h
  let idx : List (Fin (k + 1) × (Fin (r + k) → Fin (2 * r + k + 1))) :=
    ((Finset.univ : Finset (Fin (k + 1))) ×ˢ jSetR k r).toList
  have hmem : ((0 : Fin (k + 1)), rowsR k r 0) ∈ idx := by
    simp only [idx, Finset.mem_toList, Finset.mem_product, Finset.mem_univ, true_and]
    exact rim_mem
  refine ⟨rimCat Θs idx, rimCat_poly hP _, ?_, ?_⟩
  · obtain ⟨i, l, hl⟩ : ∃ i l, idx = i :: l := by
      cases h' : idx with
      | nil => rw [h'] at hmem; exact absurd hmem List.not_mem_nil
      | cons i l => exact ⟨i, l, rfl⟩
    rw [hl]
    exact rimCat_order hP hO _ _
  · intro UU F hF g hgU hg
    rw [rimCat_apply]
    simp only [idx]
    rw [Finset.sum_map_toList, Finset.sum_product]
    simp only [rvhatOp, Finset.smul_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    refine Finset.sum_congr rfl fun J _ => ?_
    rw [hR (t, J) UU F hF g hgU hg, Finset.sum_singleton, smul_smul]

end ops

theorem jDRRealInvM_of_inv (hI : JDRInvFnM) : JDRRealInvM := by
  intro ε Cc E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top A₀ hB v y
  obtain ⟨Θ, hP, hO, hR⟩ := rim_real (Wp := Wp (S.pl v)) (Wq := Wq (S.pl v)) (T v).base.z (T v).base.z' (y : ℂ) ε
  have hn : 0 < 2 * S.G.r + S.G.k + 1 := by omega
  refine ⟨Θ, QMinOp.polyOp_mono hP (by omega) (Nat.le_mul_of_pos_left _ (by omega)), ?_, ?_⟩
  · intro p hp F hF g hg
    rw [hO] at hF
    have hgG : g ∈ B.GV S.G.k S.G.r := hg.1
    have hsg : B.sgs p g ∈ B.GV S.G.k S.G.r := Formalism.FourierDecayAlt.P.B6.conj_product_mem_unitary_group (T v).base hp hgG
    rw [hR _ _ (Formalism.FourierDecayAlt.P.B5.ckOn_rho (T v).base hp hF) g hgG hgG]
    have e2 : B.rho (T v).base p (B.opApply Θ F) g =
        B.rho (T v).base p (fun x => ε • rvhatOp S.G.k S.G.r (T v).base.z (T v).base.z' (y : ℂ) F x) g := by
      simp only [B.rho]
      rw [hR _ _ hF _ hsg hsg]
    rw [e2, hI S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)) (T v).base (y : ℂ) p hp F hF g hg]
    simp only [B.rho, ContinuousLinearMap.comp_smul, ContinuousLinearMap.smul_comp]
  · intro U F hU hF g hg
    have hgG : g ∈ B.GV S.G.k S.G.r := by simpa [Q.Glev] using hg.1
    refine hR (Q.Glev S.G.k S.G.r 0 ∩ U) F ?_ g hg hgG
    intro g₀ hg₀
    obtain ⟨U', F', hU', hg₀U, hc, he⟩ := hF g₀ hg₀
    refine ⟨U', F', hU', hg₀U, hc.of_le (by exact_mod_cast le_top), fun x hx hxG => he x hx ?_⟩
    simpa [Q.Glev] using hxG

end

end Formalism.FourierDecayAlt.P.CutMP
end

section

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP

open NumberField Matrix

noncomputable section

section defs

variable (k r : ℕ)

def rowsNv (l : Fin (r + 1)) (s : Fin (k + 1)) : Fin (r - l.val + k) → Fin (2 * r + k + 1) :=
  fun j => ⟨if j.val < s.val then r + j.val else r + j.val + 1, by
    have := j.isLt; have := s.isLt; have := l.isLt; split_ifs <;> omega⟩

def NLv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (z z' : Fin (2 * r + k + 1) → ℂ) (l : Fin (r + 1))
    (u : ℂ) (f : Q.Mx k r → E) : Q.Mx k r → E :=
  fun g => ∑ s : Fin (k + 1), ∑ t : Fin (k + 1),
    (((-1 : ℂ) ^ ((s : ℕ) + (t : ℕ))) * herm (Hpk k r) (g *ᵥ bvec (wI k r s)) z * z' (wI k r t)) •
      qminorOp (Q.EH k r) (rowsNv k r l s) (rowsNv k r l t) u f g

def FNv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (z z' : Fin (2 * r + k + 1) → ℂ) (Y : ℂ)
    (J : Q.Mx k r → E) (l : Fin (r + 1)) : Q.Fn k r E :=
  Q.resG k r (Fin.last r) (NLv k r z z' l (Q.uC k r (Fin.last r) Y - 1) J)

end defs

def JDRvBeta : Prop :=
  ∀ k r : ℕ, ∃ σ : ℂ, σ ≠ 0 ∧ ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (z z' : Fin (2 * r + k + 1) → ℂ)
    (Y : ℂ) (f : Q.Mx k r → E), inWb k r z → ∀ c ∈ OmX r, ∀ g ∈ Q.Glev k r (Fin.last r),
      rvhatOp k r z z' Y f (Q.wCell k r (Fin.last r) c * g) =
        (σ * ∏ a, c a) • NLv k r z z' 0 (Q.uC k r (Fin.last r) Y - 1) f (Q.wCell k r (Fin.last r) c * g)

def JDRvTop : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq] [NormedSpace ℂ Wq]
    (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (π : Q.Mx k r → (Wp →L[ℂ] Wp)) (π' : Q.Mx k r → (Wq →L[ℂ] Wq))
    (D : Set (Q.Mx k r)) (Y : ℂ), inWb k r z → inWb k r z' → Q.IsDom k r z z' 0 D →
    ∀ J ∈ Q.FFl k r z z' π π' 0 D, ∀ c ∈ OmX r, ∀ g ∈ Q.Glev k r (Fin.last r), Q.wCell k r (Fin.last r) c * g ∈ D →
      FNv k r z z' Y J (Fin.last r) c g = -Q.QL k r z z' (Fin.last r) Y 0 1 (Q.resG k r (Fin.last r) J) c g

def JDRvStepA : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq] [NormedSpace ℂ Wq]
    (k r : ℕ) (hr : 1 ≤ r) (z z' : Fin (2 * r + k + 1) → ℂ) (π : Q.Mx k r → (Wp →L[ℂ] Wp))
    (π' : Q.Mx k r → (Wq →L[ℂ] Wq)) (D : Set (Q.Mx k r)) (Y : ℂ), inWb k r z → inWb k r z' → Q.IsDom k r z z' 0 D →
    ∀ J ∈ Q.FFl k r z z' π π' 0 D, ∀ c ∈ OmX r, ∀ g ∈ Q.Glev k r (Fin.last r), Q.wCell k r (Fin.last r) c * g ∈ D →
      FNv k r z z' Y J ⟨r - 1, by omega⟩ c g =
        (Y • FNv k r z z' Y J (Fin.last r) - Q.crd (Formalism.QuantumDeterminants.pbOp ⟨r - 1, by omega⟩) (FNv k r z z' Y J (Fin.last r)) -
          Q.crd (Formalism.QuantumDeterminants.cbiOp ⟨r - 1, by omega⟩) (Q.QL k r z z' (Fin.last r) Y 1 1 (Q.resG k r (Fin.last r) J))) c g

def JDRvStepB : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq] [NormedSpace ℂ Wq]
    (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (π : Q.Mx k r → (Wp →L[ℂ] Wp)) (π' : Q.Mx k r → (Wq →L[ℂ] Wq))
    (D : Set (Q.Mx k r)) (Y : ℂ), inWb k r z → inWb k r z' → Q.IsDom k r z z' 0 D →
    ∀ J ∈ Q.FFl k r z z' π π' 0 D, ∀ (l : ℕ) (hl : l + 2 ≤ r),
    ∀ c ∈ OmX r, ∀ g ∈ Q.Glev k r (Fin.last r), Q.wCell k r (Fin.last r) c * g ∈ D →
      FNv k r z z' Y J ⟨l, by omega⟩ c g =
        (Y • FNv k r z z' Y J ⟨l + 1, by omega⟩ -
          Q.crd (Formalism.QuantumDeterminants.pbOp ⟨l, by omega⟩) (FNv k r z z' Y J ⟨l + 1, by omega⟩) -
          Q.crd (Formalism.QuantumDeterminants.cbOp ⟨l + 1, by omega⟩) (Q.crd (Formalism.QuantumDeterminants.cbiOp ⟨l, by omega⟩)
            (FNv k r z z' Y J ⟨l + 2, by omega⟩))) c g

def JDRvChainM : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq] [NormedSpace ℂ Wq]
    (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (π : Q.Mx k r → (Wp →L[ℂ] Wp)) (π' : Q.Mx k r → (Wq →L[ℂ] Wq))
    (D : Set (Q.Mx k r)) (Y : ℂ), inWb k r z → inWb k r z' → Q.IsDom k r z z' 0 D →
    ∀ J ∈ Q.FFl k r z z' π π' 0 D, ∀ c ∈ OmX r, ∀ g ∈ Q.Glev k r (Fin.last r), Q.wCell k r (Fin.last r) c * g ∈ D →
      FNv k r z z' Y J 0 c g =
        -(Q.QL k r z z' (Fin.last r) Y 0 1 (Q.crd (Q.cmp (Q.vABs r Y r) 0) (Q.resG k r (Fin.last r) J)) +
          Q.QL k r z z' (Fin.last r) Y 1 1 (Q.crd (Q.cmp (Q.vABs r Y r) 1) (Q.resG k r (Fin.last r) J))) c g

def JDRvConseq : Prop := JDRvTop → JDRvStepA → JDRvStepB → JDRvChainM

theorem jDRRadM_of_parts (hB : JDRvBeta) (hT : JDRvTop) (hA : JDRvStepA) (hS : JDRvStepB) (hC : JDRvConseq) :
    JDRRadM := by
  have hCh := hC hT hA hS
  intro k r
  obtain ⟨σ, hσ, hβ⟩ := hB k r
  refine ⟨-σ⁻¹, ?_⟩
  intro Wp Wq _ _ _ _ z z' π π' D Y hz hz' hD J hJ c hc g hg hcg
  have h1 := hβ (Wq →L[ℂ] Wp) z z' Y J hz c hc g hg
  have h2 := hCh Wp Wq k r z z' π π' D Y hz hz' hD J hJ c hc g hg hcg
  simp only [FNv, Q.resG] at h2
  simp only [Q.resG, rhvGrp, dMul, drF]
  rw [h1, smul_smul, smul_smul, show ∀ a b : ℂ, a * -σ⁻¹ * (σ * b) = -b * a from fun a b => by field_simp,
    ← smul_smul, h2, smul_neg, neg_smul, neg_neg]

end

end Formalism.FourierDecayAlt.P.CutMP
end

section

open Matrix MeasureTheory Filter Topology

noncomputable section

namespace Formalism.FourierDecayAlt.P5.HerC

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.P5.HerA Formalism.FourierDecayAlt.P5.HerB

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section Minors

variable {k r : ℕ}

def pc (c : Fin r → ℂ) : ℂ := ∏ a : Fin r with a.val < (Fin.last r).val, c a

theorem pc_continuous : Continuous (pc (r := r)) := by
  unfold pc
  exact continuous_finsetProd _ fun a _ => continuous_apply a

theorem pc_ne_zero {c : Fin r → ℂ} (hc : c ∈ OmX r) : pc c ≠ 0 := Finset.prod_ne_zero_iff.2 fun a _ => hc a

theorem dmin_wCell {z z' : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (hz' : inWb k r z') {c : Fin r → ℂ}
    (hc : c ∈ OmX r) {g : Mx k r} (hg : g ∈ Glev k r (Fin.last r)) :
    Dmin k r z z' (wCell k r (Fin.last r) c * g) ⟨r, by omega⟩ = pc c ∧
      Dmin k r z z' (wCell k r (Fin.last r) c * g) (Fin.last (r + 1)) = zetaL k r z z' (Fin.last r) g * pc c := by
  obtain ⟨μ, _, rfl⟩ := (Formalism.FourierDecayAlt.P.TwoByOneBlock.UWb_iff g).1 (Formalism.FourierDecayAlt.P5.Rad.glev_last_uwb hg)
  have e : wCell k r (Fin.last r) c * Formalism.FourierDecayAlt.B2.embWb k r μ = bigCell k r c μ := by
    rw [Formalism.FourierDecayAlt.P5.Rad.wCell_last_eq, ← (Formalism.FourierDecayAlt.P.bruhat_big_cell_factorization k r c μ).1]
  rw [e]
  have hmin := big_cell_minors_holds k r z z' c μ hz hz'
  have hζ : herm (Hpk k r) (bigCell k r c μ *ᵥ z') z = zetaL k r z z' (Fin.last r) (Formalism.FourierDecayAlt.B2.embWb k r μ) := by
    rw [Formalism.FourierDecayAlt.P5.Rad.zetaL_last, ← Formalism.FourierDecayAlt.P.TwoByOneBlock.jV_wbPart hz', Formalism.FourierDecayAlt.P.BigCellHermitian.bigCell_mulVec_jV,
      Formalism.FourierDecayAlt.P.TwoByOneBlock.emb_mulVec_jV]
  have hr : Dmin k r z z' (bigCell k r c μ) ⟨r, by omega⟩ = pc c := hmin.1 (Fin.last r)
  refine ⟨hr, ?_⟩
  have hzeta := hmin.2.2 hc
  rw [hζ] at hzeta
  unfold Formalism.QuantumDeterminants.zeta at hzeta
  rw [hr] at hzeta
  have h2 := div_mul_cancel₀ (Dmin k r z z' (bigCell k r c μ) (Fin.last (r + 1))) (pc_ne_zero hc)
  rw [hzeta] at h2
  exact h2.symm

end Minors

theorem jfCptLocAll : JFCptLocAll := by
  intro Wp Wq _ _ _ _ _ _ P z z' π π' D F Φ _hP hz hz' hπ hπ' hF hΦ
  subst hz hz' hπ hπ'
  obtain ⟨⟨_, ε, hε, hG⟩, hC⟩ := hF
  have hW := Formalism.FourierDecayAlt.P.weyl_subgroup_closed P.k P.r
  have hN := Formalism.FourierDecayAlt.P.unipotent_radical_closed P.k P.r
  have hGV := Formalism.FourierDecayAlt.P.unitary_group_closed P.k P.r
  have := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite D.haarW
  have := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite D.haarN
  have := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite D.haarW'

  have hcont : Continuous (fun h : Mx P.k P.r => Dmin P.k P.r D.z D.z' h (Fin.last (P.r + 1))) :=
    (Formalism.FourierDecayAlt.P.JCx1.contDiff_Dmin D.z D.z' (Fin.last (P.r + 1))).continuous
  obtain ⟨R0, hR0⟩ := hC.isCompact.exists_bound_of_continuousOn hcont.continuousOn

  have hae : ∀ᵐ (p : (Mt P.k P.r × Mt P.k P.r) × (Mt P.k P.r × Mt P.k P.r)) ∂((D.μW.prod D.μN).prod (D.μW'.prod D.μN)),
      (Matrix.of p.1.1 ∈ UWset P.k P.r D.z ∧ Matrix.of p.1.2 ∈ Formalism.QuantumDeterminants.Nset P.k P.r) ∧
        (Matrix.of p.2.1 ∈ UWset P.k P.r D.z' ∧ Matrix.of p.2.2 ∈ Formalism.QuantumDeterminants.Nset P.k P.r) := by
    have hw : ∀ᵐ (a : Mt P.k P.r) ∂D.μW, Matrix.of a ∈ UWset P.k P.r D.z :=
      (measure_eq_zero_iff_ae_notMem.1 D.haarW.conc).mono fun a ha => not_not.1 ha
    have hn : ∀ᵐ (a : Mt P.k P.r) ∂D.μN, Matrix.of a ∈ Formalism.QuantumDeterminants.Nset P.k P.r :=
      (measure_eq_zero_iff_ae_notMem.1 D.haarN.conc).mono fun a ha => not_not.1 ha
    have hw' : ∀ᵐ (a : Mt P.k P.r) ∂D.μW', Matrix.of a ∈ UWset P.k P.r D.z' :=
      (measure_eq_zero_iff_ae_notMem.1 D.haarW'.conc).mono fun a ha => not_not.1 ha
    have h1 : ∀ᵐ (q : Mt P.k P.r × Mt P.k P.r) ∂(D.μW.prod D.μN), Matrix.of q.1 ∈ UWset P.k P.r D.z ∧ Matrix.of q.2 ∈ Formalism.QuantumDeterminants.Nset P.k P.r :=
      (Measure.quasiMeasurePreserving_fst.ae hw).and (Measure.quasiMeasurePreserving_snd.ae hn)
    have h2 : ∀ᵐ (q : Mt P.k P.r × Mt P.k P.r) ∂(D.μW'.prod D.μN), Matrix.of q.1 ∈ UWset P.k P.r D.z' ∧ Matrix.of q.2 ∈ Formalism.QuantumDeterminants.Nset P.k P.r :=
      (Measure.quasiMeasurePreserving_fst.ae hw').and (Measure.quasiMeasurePreserving_snd.ae hn)
    exact (Measure.quasiMeasurePreserving_fst.ae h1).and (Measure.quasiMeasurePreserving_snd.ae h2)
  intro c hc
  set p0 : ℝ := ‖pc c‖ with hp0
  have hp0pos : 0 < p0 := norm_pos_iff.2 (pc_ne_zero hc)
  set U : Set (Fin P.r → ℂ) := {c' | p0 / 2 < ‖pc c'‖ ∧ ‖pc c'‖ < 2 * p0} with hU
  have hUo : IsOpen U :=
    (isOpen_lt continuous_const (continuous_norm.comp pc_continuous)).inter
      (isOpen_lt (continuous_norm.comp pc_continuous) continuous_const)
  have hcU : c ∈ U := ⟨by linarith, by linarith⟩
  set e' : ℝ := ε / (2 * p0) ^ 2 with he'
  set R' : ℝ := R0 / (p0 / 2) with hR'
  have he'pos : 0 < e' := div_pos hε (by positivity)
  refine ⟨U, hUo, hcU, {g | g ∈ Glev P.k P.r (Fin.last P.r) ∧ e' ≤ GGl P.k P.r D.z D.z' g ∧
      ‖zetaL P.k P.r D.z D.z' (Fin.last P.r) g‖ ≤ R'},
    isCompact_zeta_le D.z D.z' D.z_mem D.z'_mem D.T_pos D.T'_pos e' R', fun g hg => lt_of_lt_of_le he'pos hg.2.1, ?_⟩
  intro c' hc' g hg hgK
  by_cases hd : (c', g) ∈ DomR P.k P.r D.z D.z'
  swap
  · exact radSp_zero_off Φ (x := (c', g)) hd
  rw [hΦ (c', g) hd]
  unfold resG
  have hc'O : c' ∈ OmX P.r := hd.1
  set x : Mx P.k P.r := wCell P.k P.r (Fin.last P.r) c' * g with hx
  obtain ⟨hDr, hDl⟩ := dmin_wCell D.z_mem D.z'_mem hc'O hg
  rw [← hx] at hDr hDl
  have hxG : x ∈ B.GV P.k P.r := hGV.mul_mem _ (Formalism.FourierDecayAlt.P.Qx3.wlist_glev hc'O _).1 _ hg.1

  have hF0 : ∀ y ∈ B.GV P.k P.r, Dmin P.k P.r D.z D.z' y ⟨P.r, by omega⟩ = pc c' →
      Dmin P.k P.r D.z D.z' y (Fin.last (P.r + 1)) = zetaL P.k P.r D.z D.z' (Fin.last P.r) g * pc c' → F y = 0 := by
    intro y hy hyr hyl
    by_contra hFy
    apply hgK
    have hsupp : y ∈ tsupport F := subset_tsupport F hFy
    have hb := hR0 y hsupp
    have hGy := hG y hy hFy
    rw [hyl] at hb
    have hGy' : Gf P.k P.r D.z D.z' y = Complex.normSq (pc c') * GGl P.k P.r D.z D.z' g := by
      unfold Formalism.QuantumDeterminants.Gf GGl
      rw [hyr, hyl, Complex.normSq_mul]
      ring
    have hpc1 : p0 / 2 < ‖pc c'‖ := hc'.1
    have hpc2 : ‖pc c'‖ < 2 * p0 := hc'.2
    have hpcpos : 0 < ‖pc c'‖ := by linarith
    have hns : Complex.normSq (pc c') = ‖pc c'‖ ^ 2 := by rw [Complex.sq_norm]
    refine ⟨hg, ?_, ?_⟩
    ·
      have hGG : ε ≤ ‖pc c'‖ ^ 2 * GGl P.k P.r D.z D.z' g := by rw [← hns, ← hGy']; exact hGy
      have hGGpos : 0 < GGl P.k P.r D.z D.z' g := hd.2.2
      have hsq : ‖pc c'‖ ^ 2 ≤ (2 * p0) ^ 2 := by nlinarith
      rw [he', div_le_iff₀ (by positivity)]
      nlinarith
    ·
      rw [norm_mul] at hb
      have hz0 : 0 ≤ ‖zetaL P.k P.r D.z D.z' (Fin.last P.r) g‖ := norm_nonneg _
      rw [hR', le_div_iff₀ (by positivity)]
      nlinarith
  have hJ0 : B.JF D F x = 0 := by
    unfold B.JF besselJ
    refine integral_eq_zero_of_ae (hae.mono fun p hp => ?_)
    obtain ⟨⟨ha, hn⟩, ⟨ha', hn'⟩⟩ := hp
    set a := Matrix.of p.1.1
    set n := Matrix.of p.1.2
    set a' := Matrix.of p.2.1
    set n' := Matrix.of p.2.2
    have hainv : a⁻¹ ∈ UWset P.k P.r D.z := (hW D.z).inv_mem _ ha
    have hninv : n⁻¹ ∈ Formalism.QuantumDeterminants.Nset P.k P.r := hN.inv_mem _ hn
    have hs1 : a⁻¹ * n⁻¹ ∈ Formalism.QuantumDeterminants.Sset P.k P.r D.z := ⟨a⁻¹, hainv, n⁻¹, hninv, rfl⟩
    have hs2 : n' ∈ Formalism.QuantumDeterminants.Sset P.k P.r D.z' := ⟨1, (hW D.z').one_mem, n', hn', (one_mul _).symm⟩
    have hs3 : (1 : Mx P.k P.r) ∈ Formalism.QuantumDeterminants.Sset P.k P.r D.z := ⟨1, (hW D.z).one_mem, 1, hN.one_mem, (mul_one _).symm⟩
    have hs4 : a' ∈ Formalism.QuantumDeterminants.Sset P.k P.r D.z' := ⟨a', ha', 1, hN.one_mem, (mul_one _).symm⟩
    have hinvD : ∀ l, Dmin P.k P.r D.z D.z' (a⁻¹ * n⁻¹ * x * n' * a') l = Dmin P.k P.r D.z D.z' x l := by
      intro l
      have e1 := diagonal_inverse_holds P.k P.r D.z D.z' D.z_mem D.z'_mem 1 hs3 a' hs4 (a⁻¹ * n⁻¹ * x * n') l
      rw [one_mul] at e1
      rw [e1]
      exact diagonal_inverse_holds P.k P.r D.z D.z' D.z_mem D.z'_mem _ hs1 n' hs2 x l
    have hyG : a⁻¹ * n⁻¹ * x * n' * a' ∈ B.GV P.k P.r :=
      hGV.mul_mem _ (hGV.mul_mem _ (hGV.mul_mem _ (hGV.mul_mem _ hainv.1 _ hninv.1) _ hxG) _ hn'.1) _ ha'.1
    have hFy : F (a⁻¹ * n⁻¹ * x * n' * a') = 0 :=
      hF0 _ hyG (by rw [hinvD]; exact hDr) (by rw [hinvD]; exact hDl)
    have hxy : (Matrix.of p.1.1)⁻¹ * (Matrix.of p.1.2)⁻¹ * x * Matrix.of p.2.2 * Matrix.of p.2.1 =
        a⁻¹ * n⁻¹ * x * n' * a' := rfl
    simp only [hxy, hFy, ContinuousLinearMap.comp_zero, ContinuousLinearMap.zero_comp, smul_zero, Pi.zero_apply]
  rw [hJ0, smul_zero]

theorem thmPActualCpt_of_stepForm (hSF : StepFormCptAll) : ThmPActualCpt := thmPActualCpt_of_jf jfCptLocAll hSF

end Formalism.FourierDecayAlt.P5.HerC
end
end
