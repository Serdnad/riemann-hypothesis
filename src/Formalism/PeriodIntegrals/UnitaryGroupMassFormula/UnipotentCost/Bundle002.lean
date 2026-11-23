module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnipotentCost.LetterSize
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.BetaSesquilinearity
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
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
import Mathlib.Order.CompletePartialOrder
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P.BetaSesquilinearity
open scoped ContDiff

noncomputable section

namespace PI.UnitaryGroupMassFormula.UsCost.GrothendieckCommutativity

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

noncomputable local instance clmNACG : NormedAddCommGroup (B.Mat k r →L[ℝ] E) :=
  ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance clmNS : NormedSpace ℝ (B.Mat k r →L[ℝ] E) :=
  ContinuousLinearMap.toNormedSpace

lemma fderiv_apply_lin {f' : B.Mat k r → E} {U : Set (B.Mat k r)} (hU : IsOpen U)
    (hc : ContDiffOn ℝ 2 f' U) {g : B.Mat k r} (hg : g ∈ U) (A : B.Mat k r →L[ℝ] B.Mat k r) :
    DifferentiableAt ℝ (fun y => fderiv ℝ f' y (A y)) g ∧
    ∀ V, fderiv ℝ (fun y => fderiv ℝ f' y (A y)) g V =
      fderiv ℝ f' g (A V) + fderiv ℝ (fderiv ℝ f') g V (A g) := by
  have h1 : ContDiffOn ℝ 1 (fun y => fderiv ℝ f' y) U :=
    hc.fderiv_of_isOpen hU (by first | norm_num | rfl | simp)
  have hd : DifferentiableAt ℝ (fderiv ℝ f') g :=
    (h1.differentiableOn one_ne_zero).differentiableAt (hU.mem_nhds hg)
  have hA : DifferentiableAt ℝ (fun y => A y) g := A.differentiableAt
  refine ⟨hd.clm_apply hA, fun V => ?_⟩
  have key := (hd.hasFDerivAt.clm_apply A.hasFDerivAt).fderiv
  exact (congrArg (fun L => L V) key).trans rfl

lemma swap1 {X Y : B.Mat k r} (hX : B.inLie k r X) (hY : B.inLie k r Y) {h : B.Mat k r → E}
    (hh : B.CkOn 2 (B.GV k r) h) {g : B.Mat k r} (hg : g ∈ B.GV k r) :
    Dx (false, X) (Dx (true, Y) h) g = Dx (true, Y) (Dx (false, X) h) g := by
  have hdx : ∀ (x : Bool × B.Mat k r), B.inLie k r x.2 → ∀ {f f' : B.Mat k r → E} {U : Set (B.Mat k r)},
      IsOpen U → (∀ y ∈ U, y ∈ B.GV k r → f y = f' y) → ∀ y ∈ U, y ∈ B.GV k r →
      DifferentiableAt ℝ f' y → Dx x f y = fderiv ℝ f' y (dirL x y) := by
    intro x hx f f' U hU hff y hyU hy hd
    rw [Dx_eq, dirL_apply]
    exact (Dx_hasDerivAt hx hU hyU hy hd hff).deriv
  obtain ⟨U, h', hU, hgU, hc, heq⟩ := hh g hg
  have hc2 : ContDiffOn ℝ 2 h' U := by exact_mod_cast hc
  have hdiff : ∀ y ∈ U, DifferentiableAt ℝ h' y := fun y hy =>
    (hc2.differentiableOn (by norm_num)).differentiableAt (hU.mem_nhds hy)
  obtain ⟨hdL, hfL⟩ := fderiv_apply_lin hU hc2 hgU (dirL (true, Y))
  obtain ⟨hdR, hfR⟩ := fderiv_apply_lin hU hc2 hgU (dirL (false, X))
  have e1 : Dx (false, X) (Dx (true, Y) h) g =
      Dx (false, X) (fun y => fderiv ℝ h' y (dirL (true, Y) y)) g :=
    Dx_congr_loc (x := (false, X)) hX hU
      (fun y hy hyU => hdx (true, Y) hY hU heq y hyU hy (hdiff y hyU)) g hg hgU
  have e2 : Dx (true, Y) (Dx (false, X) h) g =
      Dx (true, Y) (fun y => fderiv ℝ h' y (dirL (false, X) y)) g :=
    Dx_congr_loc (x := (true, Y)) hY hU
      (fun y hy hyU => hdx (false, X) hX hU heq y hyU hy (hdiff y hyU)) g hg hgU
  rw [e1, e2, hdx (false, X) hX hU (fun _ _ _ => rfl) g hgU hg hdL,
    hdx (true, Y) hY hU (fun _ _ _ => rfl) g hgU hg hdR, hfL, hfR]
  have hsymm : IsSymmSndFDerivAt ℝ h' g :=
    (hc2.contDiffAt (hU.mem_nhds hgU)).isSymmSndFDerivAt (by simp)
  rw [show dirL (true, Y) (dirL (false, X) g) = dirL (false, X) (dirL (true, Y) g) by
      simp [dirL_apply, dirv, mul_assoc]]
  congr 1
  exact hsymm _ _

lemma ckDw {w : List (Bool × B.Mat k r)} (hw : ∀ x ∈ w, B.inLie k r x.2) {f : B.Mat k r → E} {m n : ℕ}
    (hf : B.CkOn (n : ℕ∞) (B.GV k r) f) (hmn : m + w.length ≤ n) : B.CkOn (m : ℕ∞) (B.GV k r) (Dw w f) := by
  exact Formalism.FourierDecayAlt.P.BetaSesquilinearity.CkOn_Dw hw (Formalism.FourierDecayAlt.P.BetaSesquilinearity.sCkOn_mono (by exact_mod_cast hmn) hf)

lemma len_wL (u : List (B.Mat k r)) : (wL u).length = u.length := by
  simp [wL]

lemma len_wR (v : List (B.Mat k r)) : (wR v).length = v.length := by
  simp [wR]

lemma lie_wL {u : List (B.Mat k r)} (hu : ∀ X ∈ u, B.inLie k r X) : ∀ x ∈ wL u, B.inLie k r x.2 := by
  intro x hx
  simp only [wL, List.mem_map] at hx
  obtain ⟨X, hX, rfl⟩ := hx
  exact hu X hX

lemma lie_wR {v : List (B.Mat k r)} (hv : ∀ X ∈ v, B.inLie k r X) : ∀ x ∈ wR v, B.inLie k r x.2 := by
  intro x hx
  simp only [wR, List.mem_map] at hx
  obtain ⟨X, hX, rfl⟩ := hx
  exact hv X hX

lemma moveR {X : B.Mat k r} (hX : B.inLie k r X) : ∀ (u : List (B.Mat k r)), (∀ Y ∈ u, B.inLie k r Y) →
    ∀ {h : B.Mat k r → E}, B.CkOn ((u.length + 1 : ℕ) : ℕ∞) (B.GV k r) h →
    ∀ g ∈ B.GV k r, Dx (false, X) (Dw (wL u) h) g = Dw (wL u) (Dx (false, X) h) g
  | [], _, _, _, _, _ => rfl
  | Y :: u, hu, h, hh, g, hg => by
    have hY : B.inLie k r Y := hu Y (by simp)
    have hu' : ∀ Z ∈ u, B.inLie k r Z := fun Z hZ => hu Z (List.mem_cons_of_mem Y hZ)
    show Dx (false, X) (Dx (true, Y) (Dw (wL u) h)) g = Dx (true, Y) (Dw (wL u) (Dx (false, X) h)) g
    have h2 : B.CkOn ((2 : ℕ) : ℕ∞) (B.GV k r) (Dw (wL u) h) :=
      ckDw (lie_wL hu') hh (by rw [len_wL]; simp; omega)
    rw [swap1 hX hY (by exact_mod_cast h2) hg]
    have hh' : B.CkOn ((u.length + 1 : ℕ) : ℕ∞) (B.GV k r) h :=
      sCkOn_mono (by exact_mod_cast (by simp : u.length + 1 ≤ (Y :: u).length + 1)) hh
    exact Dx_congr (x := (true, Y)) hY (moveR hX u hu' hh') g hg

lemma rightRegularAction_list_dLR_eq_append {f : B.Mat k r → E} {m : ℕ} (hf : B.CkOn (m : ℕ∞) (B.GV k r) f) (u v : List (B.Mat k r))
    (hu : ∀ X ∈ u, B.inLie k r X) (hv : ∀ X ∈ v, B.inLie k r X) :
    ∀ w : List (B.Mat k r), (∀ X ∈ w, B.inLie k r X) → u.length + v.length + w.length ≤ m →
      ∀ g ∈ B.GV k r, B.Rw w (B.dLR u v f) g = B.dLR u (w ++ v) f g
  | [], _, _, _, _ => rfl
  | X :: w, hw, hm, g, hg => by
    have hX : B.inLie k r X := hw X (by simp)
    have hw' : ∀ Z ∈ w, B.inLie k r Z := fun Z hZ => hw Z (List.mem_cons_of_mem X hZ)
    have hm' : u.length + v.length + w.length ≤ m := by simp at hm; omega
    have e1 : ∀ F : B.Mat k r → E, Formalism.REAL.RdV X F = Dx (false, X) F := fun F => by simp [Dx]
    show Formalism.REAL.RdV X (B.Rw w (B.dLR u v f)) g = B.dLR u (X :: (w ++ v)) f g
    rw [e1, Dx_congr (x := (false, X)) hX (rightRegularAction_list_dLR_eq_append hf u v hu hv w hw' hm') g hg]
    simp only [dLR_eq, Dw_append, Dw_wR]
    have hck : B.CkOn ((u.length + 1 : ℕ) : ℕ∞) (B.GV k r) (B.Rw (w ++ v) f) := by
      rw [← Dw_wR]
      refine ckDw (lie_wR ?_) hf ?_
      · intro Z hZ
        rcases List.mem_append.mp hZ with h | h
        · exact hw' Z h
        · exact hv Z h
      · rw [len_wR, List.length_append]; simp at hm; omega
    rw [moveR hX u hu hck g hg]
    rfl

end PI.UnitaryGroupMassFormula.UsCost.GrothendieckCommutativity

namespace PI.UnitaryGroupMassFormula.UsCost

theorem commLR : CommLR := by
  unfold CommLR
  intro k r E _ _ f m hf u v w hu hv hw hlen g hg
  exact GrothendieckCommutativity.rightRegularAction_list_dLR_eq_append hf u v hu hv w hw hlen g hg

end PI.UnitaryGroupMassFormula.UsCost
end
end

section

open Matrix
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U

noncomputable section

namespace PI.UnitaryGroupMassFormula.UsCost

theorem continuous_block_matrix_three {X : Type*} [TopologicalSpace X] {k j ρ : ℕ}
    {A11 : X → Matrix (Fin j) (Fin j) ℂ} {A12 : X → Matrix (Fin j) (Fin (2 * ρ + k + 1)) ℂ}
    {A13 : X → Matrix (Fin j) (Fin j) ℂ} {A21 : X → Matrix (Fin (2 * ρ + k + 1)) (Fin j) ℂ}
    {A22 : X → B.Mat k ρ} {A23 : X → Matrix (Fin (2 * ρ + k + 1)) (Fin j) ℂ}
    {A31 : X → Matrix (Fin j) (Fin j) ℂ} {A32 : X → Matrix (Fin j) (Fin (2 * ρ + k + 1)) ℂ}
    {A33 : X → Matrix (Fin j) (Fin j) ℂ}
    (h11 : Continuous A11) (h12 : Continuous A12) (h13 : Continuous A13) (h21 : Continuous A21)
    (h22 : Continuous A22) (h23 : Continuous A23) (h31 : Continuous A31) (h32 : Continuous A32)
    (h33 : Continuous A33) :
    Continuous fun x => blk3 (A11 x) (A12 x) (A13 x) (A21 x) (A22 x) (A23 x) (A31 x) (A32 x) (A33 x) := by
  refine continuous_matrix fun a b => ?_
  unfold blk3
  show Continuous fun x => fromBlocks (fromBlocks (A11 x) (A12 x) (A21 x) (A22 x))
    (fromRows (A13 x) (A23 x)) (fromCols (A31 x) (A32 x)) (A33 x)
    ((eB k j ρ).symm a) ((eB k j ρ).symm b)
  rcases (eB k j ρ).symm a with (a' | a') | a' <;> rcases (eB k j ρ).symm b with (b' | b') | b' <;>
    first
    | exact h11.matrix_elem a' b' | exact h12.matrix_elem a' b' | exact h13.matrix_elem a' b'
    | exact h21.matrix_elem a' b' | exact h22.matrix_elem a' b' | exact h23.matrix_elem a' b'
    | exact h31.matrix_elem a' b' | exact h32.matrix_elem a' b' | exact h33.matrix_elem a' b'

theorem continuous_zjH {p s : ℕ} (σ : Equiv.Perm (Fin p)) (d : Fin p → ℂ) (η : XiH p s σ) :
    Continuous fun Z' : G.Mat s => ZjH σ d η Z' := by
  unfold ZjH Zj
  refine (continuous_const.matrix_mul ?_).matrix_mul continuous_const
  refine continuous_matrix fun a b => ?_
  show Continuous fun Z' : G.Mat s => fromBlocks (headH σ d η.2.1 η.2.2) 0 0 (of Z')
    (finSumFinEquiv.symm a) (finSumFinEquiv.symm b)
  rcases finSumFinEquiv.symm a with a' | a' <;> rcases finSumFinEquiv.symm b with b' | b'
  · exact continuous_const
  · exact continuous_const
  · exact continuous_const
  · exact continuous_apply_apply a' b'

theorem det_zjH_ne {p s : ℕ} (σ : Equiv.Perm (Fin p)) (d : Fin p → ℂ) (hd : ∀ i, d i ≠ 0) (η : XiH p s σ)
    (Z : G.Mat s) (hZ : G.detM Z ≠ 0) : (ZjH σ d η Z).det ≠ 0 := by
  unfold ZjH Zj headH
  simp only [Matrix.det_mul, blk2, Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₁₂,
    Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, one_mul, mul_one]
  unfold wP lowW G.upper
  repeat' apply mul_ne_zero
  all_goals first
    | exact hZ
    | (rw [Matrix.det_diagonal]; exact Finset.prod_ne_zero_iff.2 fun i _ => hd i)
    | (have hP : (of fun a b => if σ a = b then (1 : ℂ) else 0) =
          (1 : Matrix (Fin p) (Fin p) ℂ).submatrix σ id := by
         ext a b
         simp [Matrix.one_apply]
       rw [hP, Matrix.det_permute]
       simp)
    | (first | rw [Matrix.det_of_lowerTriangular _ ?_] | rw [Matrix.det_of_lowerTriangular ?_]
       · simp
       · intro i j hij
         have hij' : i < j := hij
         simp [Matrix.one_apply, hij'.ne, not_lt.2 hij'.le])
    | (first | rw [Matrix.det_of_upperTriangular ?_] | rw [Matrix.det_of_upperTriangular _ ?_]
       · simp [G.strictUpper]
       · intro i j hij
         have hij' : j < i := hij
         simp [G.strictUpper, Matrix.one_apply, hij'.ne', not_lt.2 hij'.le])

theorem rn_mem_of (hR : RadicalParam) (k j ρ : ℕ) (x : RC k j ρ) : Rn k j ρ x ∈ B.GV k (j + ρ) := by
  unfold RadicalParam at hR
  obtain ⟨-, hrange, hsub⟩ := hR k j ρ
  have hx : Rn k j ρ x ∈ Rset k j ρ := hrange ▸ Set.mem_range_self x
  exact (hsub hx).1

theorem gaXi_mem_of (hM : SliceMem) (hR : RadicalParam) (k p s ρ : ℕ) (σ : Equiv.Perm (Fin p))
    (d : Fin p → ℂ) (hd : ∀ i, d i ≠ 0) (ξ : Xi k p s ρ σ) (Z : G.Mat s) (γ : B.Mat k ρ)
    (hZ : G.detM Z ≠ 0) (hγ : γ ∈ B.GV k ρ) : gaXi k ρ σ d ξ Z γ ∈ B.GV k (p + s + ρ) := by
  unfold gaXi
  exact Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_mul
    (Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_mul (Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_inv (rn_mem_of hR _ _ _ _))
      ((hM k (p + s) ρ).1 _ γ (det_zjH_ne σ d hd ξ.2 Z hZ) hγ)) (rn_mem_of hR _ _ _ _)

theorem gaXi_contAt (k p s ρ : ℕ) (σ : Equiv.Perm (Fin p)) (d : Fin p → ℂ) (hd : ∀ i, d i ≠ 0)
    (ξ : Xi k p s ρ σ) (Z : G.Mat s) (γ : B.Mat k ρ) (hZ : G.detM Z ≠ 0) :
    ContinuousAt (fun Z' : G.Mat s => gaXi k ρ σ d ξ Z' γ) Z := by
  have hZj := continuous_zjH σ d ξ.2 (s := s)
  have hdet : ((ZjH σ d ξ.2 Z)ᴴ).det ≠ 0 := by
    rw [Matrix.det_conjTranspose]; exact star_ne_zero.2 (det_zjH_ne σ d hd ξ.2 Z hZ)
  have hinvC : ContinuousAt Ring.inverse ((ZjH σ d ξ.2 Z)ᴴ).det := by
    simpa using NormedRing.inverse_continuousAt (Units.mk0 _ hdet)
  have hinv : ContinuousAt (fun Z' : G.Mat s => (ZjH σ d ξ.2 Z')ᴴ⁻¹) Z :=
    ContinuousAt.comp (g := (Inv.inv : Matrix (Fin (p + s)) (Fin (p + s)) ℂ → _))
      (f := fun Z' : G.Mat s => (ZjH σ d ξ.2 Z')ᴴ) (continuousAt_matrix_inv _ hinvC)
      hZj.matrix_conjTranspose.continuousAt
  let F : Matrix (Fin (p + s)) (Fin (p + s)) ℂ × Matrix (Fin (p + s)) (Fin (p + s)) ℂ → B.Mat k (p + s + ρ) :=
    fun P => (Rn k (p + s) ρ ξ.1.1)⁻¹ *
      blk3 0 0 (P.2 * G.wMat (p + s)) 0 γ 0 (G.wMat (p + s) * P.1) 0 0 * Rn k (p + s) ρ ξ.1.2
  have hF : Continuous F := by
    refine Continuous.matrix_mul (Continuous.matrix_mul continuous_const ?_) continuous_const
    exact continuous_block_matrix_three continuous_const continuous_const
      (continuous_snd.matrix_mul continuous_const) continuous_const continuous_const continuous_const
      (continuous_const.matrix_mul continuous_fst) continuous_const continuous_const
  have : (fun Z' : G.Mat s => gaXi k ρ σ d ξ Z' γ) =
      F ∘ fun Z' => (ZjH σ d ξ.2 Z', (ZjH σ d ξ.2 Z')ᴴ⁻¹) := by
    funext Z'; rfl
  rw [this]
  exact hF.continuousAt.comp (hZj.continuousAt.prodMk hinv)

theorem offK : OffK := by
  intro hM hR k p s ρ σ d hd E _ _ H O hO hH ξ Z γ hZ hγ hgO q
  have hev : (fun Z' : G.Mat s => H (gaXi k ρ σ d ξ Z' γ)) =ᶠ[nhds Z] fun _ => (0 : E) := by
    have h1 : ∀ᶠ Z' in nhds Z, gaXi k ρ σ d ξ Z' γ ∈ O :=
      (gaXi_contAt k p s ρ σ d hd ξ Z γ hZ) (hO.mem_nhds hgO)
    have hdc : Continuous fun Z' : G.Mat s => G.detM Z' := by
      unfold G.detM; exact Continuous.matrix_det continuous_id
    have h2 : ∀ᶠ Z' in nhds Z, G.detM Z' ≠ 0 := hdc.continuousAt.eventually_ne hZ
    filter_upwards [h1, h2] with Z' h1 h2
    exact hH _ (gaXi_mem_of hM hR k p s ρ σ d hd ξ Z' γ h2 hγ) h1
  refine ⟨contDiffAt_const.congr_of_eventuallyEq hev, ?_⟩
  rw [(hev.iteratedFDeriv ℝ q).eq_of_nhds]
  simp

end PI.UnitaryGroupMassFormula.UsCost
end
end

section

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U

noncomputable section

namespace PI.UnitaryGroupMassFormula.UsCost

lemma lsz_pos {k r : ℕ} (X : B.Mat k r) : 0 < lsz X := lt_of_lt_of_le one_pos (le_max_left _ _)

def sc {k r : ℕ} (X : B.Mat k r) : B.Mat k r := (((lsz X)⁻¹ : ℝ) : ℂ) • X

lemma sc_back {k r : ℕ} (X : B.Mat k r) : ((lsz X : ℝ) : ℂ) • sc X = X := by
  unfold sc
  rw [smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ (lsz_pos X).ne', Complex.ofReal_one, one_smul]

lemma entry_le_lsz {k r : ℕ} (X : B.Mat k r) (a b : Fin (2 * r + k + 1)) : ‖X a b‖ ≤ lsz X := by
  calc ‖X a b‖ = ‖(Matrix.of.symm X) a b‖ := rfl
    _ ≤ ‖(Matrix.of.symm X) a‖ := norm_le_pi_norm _ b
    _ ≤ ‖Matrix.of.symm X‖ := norm_le_pi_norm _ a
    _ ≤ lsz X := le_max_right _ _

lemma sc_entry {k r : ℕ} (X : B.Mat k r) (a b : Fin (2 * r + k + 1)) : ‖sc X a b‖ ≤ 1 := by
  have hp := lsz_pos X
  have h := entry_le_lsz X a b
  have e : sc X a b = (((lsz X)⁻¹ : ℝ) : ℂ) * X a b := rfl
  rw [e, norm_mul, Complex.norm_of_nonneg (inv_nonneg.2 hp.le), inv_mul_le_iff₀ hp, mul_one]
  exact h

lemma sc_inLieP {k j ρ : ℕ} {X : B.Mat k (j + ρ)} (hX : inLieP k j ρ X) : inLieP k j ρ (sc X) := by
  obtain ⟨h1, h2⟩ := hX
  have hs : star ((((lsz X)⁻¹ : ℝ) : ℂ)) = (((lsz X)⁻¹ : ℝ) : ℂ) := Complex.conj_ofReal _
  refine ⟨?_, fun i b hb hi => ?_⟩
  · unfold B.inLie at h1 ⊢
    unfold sc
    rw [Matrix.conjTranspose_smul, hs, Matrix.smul_mul, Matrix.mul_smul, ← smul_add, h1, smul_zero]
  · have e : sc X i b = (((lsz X)⁻¹ : ℝ) : ℂ) * X i b := rfl
    rw [e, h2 i b hb hi, mul_zero]

def scx {k r : ℕ} (x : Bool × B.Mat k r) : Bool × B.Mat k r := (x.1, sc x.2)

private lemma LdV_ofReal_smul {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (c : ℝ) (Y : B.Mat k r) (F : B.Mat k r → E) (g : B.Mat k r) :
    B.LdV (((c : ℝ) : ℂ) • Y) F g = ((c : ℝ) : ℂ) • B.LdV Y F g := by
  simp only [B.LdV]
  have e : ∀ t : ℝ, ((t : ℂ) • (((c : ℝ) : ℂ) • Y)) = (((c * t : ℝ)) : ℂ) • Y := by
    intro t; rw [smul_smul]; congr 1; push_cast; ring
  simp only [e]
  rw [deriv_comp_mul_left (𝕜 := ℝ) c (fun s : ℝ => F (NormedSpace.exp (-((s : ℂ) • Y)) * g)) 0,
    mul_zero, Complex.coe_smul]

private lemma RdV_ofReal_smul {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (c : ℝ) (Y : B.Mat k r) (F : B.Mat k r → E) (g : B.Mat k r) :
    Formalism.REAL.RdV (((c : ℝ) : ℂ) • Y) F g = ((c : ℝ) : ℂ) • Formalism.REAL.RdV Y F g := by
  simp only [Formalism.REAL.RdV]
  have e : ∀ t : ℝ, ((t : ℂ) • (((c : ℝ) : ℂ) • Y)) = (((c * t : ℝ)) : ℂ) • Y := by
    intro t; rw [smul_smul]; congr 1; push_cast; ring
  simp only [e]
  rw [deriv_comp_mul_left (𝕜 := ℝ) c (fun s : ℝ => F (g * NormedSpace.exp ((s : ℂ) • Y))) 0,
    mul_zero, Complex.coe_smul]

private lemma Dx_eq_lsz_smul_Dx_scx {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (x : Bool × B.Mat k r) (F : B.Mat k r → E) (g : B.Mat k r) :
    P.BetaSesquilinearity.Dx x F g = ((lsz x.2 : ℝ) : ℂ) • P.BetaSesquilinearity.Dx (scx x) F g := by
  obtain ⟨b, X⟩ := x
  have hX : X = ((lsz X : ℝ) : ℂ) • sc X := (sc_back X).symm
  cases b
  · show Formalism.REAL.RdV X F g = ((lsz X : ℝ) : ℂ) • Formalism.REAL.RdV (sc X) F g
    conv_lhs => rw [hX]
    exact RdV_ofReal_smul _ _ _ _
  · show B.LdV X F g = ((lsz X : ℝ) : ℂ) • B.LdV (sc X) F g
    conv_lhs => rw [hX]
    exact LdV_ofReal_smul _ _ _ _

lemma dw_scale {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (w : List (Bool × B.Mat k r)) (f : B.Mat k r → E) :
    P.BetaSesquilinearity.Dw w f = fun g => (((w.map (fun x => lsz x.2)).prod : ℝ) : ℂ) • P.BetaSesquilinearity.Dw (w.map scx) f g := by
  induction w with
  | nil => funext g; simp [P.BetaSesquilinearity.Dw]
  | cons x w ih =>
    funext g
    have h1 : P.BetaSesquilinearity.Dw (x :: w) f = P.BetaSesquilinearity.Dx x (P.BetaSesquilinearity.Dw w f) := rfl
    have h2 : P.BetaSesquilinearity.Dw ((x :: w).map scx) f = P.BetaSesquilinearity.Dx (scx x) (P.BetaSesquilinearity.Dw (w.map scx) f) := rfl
    rw [h1, h2, Dx_eq_lsz_smul_Dx_scx, ih]
    have h3 : P.BetaSesquilinearity.Dx (scx x) (fun g => (((w.map (fun x => lsz x.2)).prod : ℝ) : ℂ) • P.BetaSesquilinearity.Dw (w.map scx) f g)
        = fun g => (((w.map (fun x => lsz x.2)).prod : ℝ) : ℂ) • P.BetaSesquilinearity.Dx (scx x) (P.BetaSesquilinearity.Dw (w.map scx) f) g :=
      P.BetaSesquilinearity.Dw_smul _ [scx x] _
    rw [h3, List.map_cons, List.prod_cons, Complex.ofReal_mul, mul_smul]

lemma dw_scale_at {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (w : List (Bool × B.Mat k r)) (f : B.Mat k r → E) (g : B.Mat k r) :
    P.BetaSesquilinearity.Dw w f g = (((w.map (fun x => lsz x.2)).prod : ℝ) : ℂ) • P.BetaSesquilinearity.Dw (w.map scx) f g := congrFun (dw_scale w f) g

lemma map_lsz_LR {k r : ℕ} (u v : List (B.Mat k r)) :
    (P.BetaSesquilinearity.wL u ++ P.BetaSesquilinearity.wR v).map (fun x => lsz x.2) = (u ++ v).map lsz := by
  simp [P.BetaSesquilinearity.wL, P.BetaSesquilinearity.wR, List.map_map, Function.comp_def]

lemma map_scx_LR {k r : ℕ} (u v : List (B.Mat k r)) :
    (P.BetaSesquilinearity.wL u ++ P.BetaSesquilinearity.wR v).map scx = P.BetaSesquilinearity.wL (u.map sc) ++ P.BetaSesquilinearity.wR (v.map sc) := by
  simp [P.BetaSesquilinearity.wL, P.BetaSesquilinearity.wR, scx, List.map_map, Function.comp_def]

lemma dLR_scale {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (u v : List (B.Mat k r)) (f : B.Mat k r → E) (g : B.Mat k r) :
    B.dLR u v f g = ((((u ++ v).map lsz).prod : ℝ) : ℂ) • B.dLR (u.map sc) (v.map sc) f g := by
  rw [P.BetaSesquilinearity.dLR_eq, P.BetaSesquilinearity.dLR_eq, dw_scale_at (P.BetaSesquilinearity.wL u ++ P.BetaSesquilinearity.wR v), map_lsz_LR, map_scx_LR]

theorem starScale : StarScale := by
  intro k j ρ E _ _ F₁ A₁ Q B₁ K hS u v hu hv hl g hg
  have hu' : unitP k j ρ (u.map sc) := by
    intro X hX
    obtain ⟨Y, hY, rfl⟩ := List.mem_map.1 hX
    exact ⟨sc_inLieP (hu Y hY), sc_entry Y⟩
  have hv' : unitP k j ρ (v.map sc) := by
    intro X hX
    obtain ⟨Y, hY, rfl⟩ := List.mem_map.1 hX
    exact ⟨sc_inLieP (hv Y hY), sc_entry Y⟩
  have hb := hS.2.2 (u.map sc) (v.map sc) hu' hv' (by simpa using hl) g hg
  have hP : 0 ≤ ((u ++ v).map lsz).prod :=
    List.prod_nonneg (fun a ha => by obtain ⟨Y, -, rfl⟩ := List.mem_map.1 ha; exact (lsz_pos Y).le)
  rw [dLR_scale, norm_smul, Complex.norm_of_nonneg hP]
  have := mul_le_mul_of_nonneg_left hb hP
  nlinarith [this]

end PI.UnitaryGroupMassFormula.UsCost
end
end
