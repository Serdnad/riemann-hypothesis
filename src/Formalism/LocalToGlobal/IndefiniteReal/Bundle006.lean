module

public import Formalism.LocalToGlobal.IndefiniteReal.CutTuples2
public import Formalism.LocalToGlobal.Divisibility.FramesLemmas
public import Formalism.LocalToGlobal.IndefiniteReal.CxLemmas
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Finiteness.Lattice
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder InnerProductSpace

noncomputable section

namespace Formalism.IndefR.Cx

open Formalism.DivisionValues Formalism.L2.Indef Formalism.L2.DIV

variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem eq_zero_of_range_adjoint {E F : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F] (f : E →ₗ[ℂ] F) {u : E}
    (hu : u ∈ LinearMap.range (LinearMap.adjoint f)) (h0 : f u = 0) : u = 0 := by
  obtain ⟨w, rfl⟩ := hu
  have h : ⟪(LinearMap.adjoint f) w, (LinearMap.adjoint f) w⟫_ℂ = 0 := by
    rw [LinearMap.adjoint_inner_left, h0, inner_zero_right]
  exact inner_self_eq_zero.mp h

namespace CxData

variable {Bs : DefBase K} {A : DefAmb Bs} (X : CxData A) {fc : DefSub A → DefFace Bs} (cr : Crd A fc) (b : Bool)

def uL (j : Bs.J) (t : Bs.Tup) : Fin ((lv (fc X.zs) b).dZ j t) → X.FLC j t :=
  fun k => X.jL j t (cr.toL X.zs b j t (Pi.single k 1))

theorem tC_eq (j : Bs.J) (t : Bs.Tup) (c : Fin ((lv (fc X.zs) b).dZ j t) → ℂ) :
    X.tC cr b j t c = X.θ' j t (lin (X.uL cr b j t) c) := by

  simp only [tC, uL, lin, Fintype.linearCombination_apply, map_sum, map_smul]

theorem jL_toL (j : Bs.J) (t : Bs.Tup) (x : Fin ((lv (fc X.zs) b).dZ j t) → K) :
    X.jL j t (cr.toL X.zs b j t x) = lin (X.uL cr b j t) (cpt Bs.v0.embedding x) := by
  have hx : x = ∑ k, x k • (Pi.single k (1 : K) : Fin ((lv (fc X.zs) b).dZ j t) → K) := by
    ext i
    simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hx]

  simp only [map_sum, map_smul, map_smulₛₗ, lin, Fintype.linearCombination_apply, cpt, uL]

theorem lin_mem {E : Type} [AddCommGroup E] [Module ℂ E] {n : ℕ} {v : Fin n → E} {S : Submodule ℂ E}
    (h : ∀ k, v k ∈ S) (c : Fin n → ℂ) : lin v c ∈ S := by
  simp only [lin, Fintype.linearCombination_apply]
  exact Submodule.sum_mem _ fun k _ => S.smul_mem _ (h k)

theorem gram_uL (hI : X.IsoL cr b) (j : Bs.J) (t : Bs.Tup) :
    Matrix.gram ℂ (X.uL cr b j t) = ((X.nP b : ℝ) : ℂ) • metOf ((lv (fc X.zs) b).XT j t Bs.v0) := by
  ext k l
  rw [Matrix.gram_apply]
  simp only [uL]
  rw [hI j t (Pi.single k 1) (Pi.single l 1)]
  simp [Matrix.smul_apply, Formalism.HermitianLatticesTheory.majAt, Formalism.HermitianLatticesTheory.fcoord, Formalism.HermitianLatticesTheory.vecAt, metOf, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Matrix.mulVec, dotProduct, Pi.single_apply]

theorem lin_uL_injective (hW : (lv (fc X.zs) b).WF) (hn : 0 < X.nP b) (hI : X.IsoL cr b) (j : Bs.J) (t : Bs.Tup) :
    Function.Injective (lin (X.uL cr b j t)) := by
  apply lin_injective
  apply Matrix.linearIndependent_of_posDef_gram
  rw [X.gram_uL cr b hI j t]
  exact (metOfSpec _ _ ((hW.XT_herm j t).1 Bs.v0)).1.smul (Complex.zero_lt_real.mpr hn)

end CxData

namespace CxData

variable {Bs : DefBase K} {A : DefAmb Bs} (X : CxData A) {fc : DefSub A → DefFace Bs}

theorem cutLifts (cr : Crd A fc) (cv : CrdV A) (b : Bool) : X.CutLifts cr cv b := by
  intro hW hpos _hK hI hZ hV hR hDn hUp hA hP
  have hZk : ∀ j t k, X.uL cr b j t k ∈ LinearMap.range (LinearMap.adjoint (X.θ' j t)) :=
    fun j t k => hZ j t (Pi.single k 1)
  have hVk : ∀ j t k, X.uL cr b j t k ∈ X.goodPartComplexPoints cv b j t :=
    fun j t k => Submodule.subset_span ⟨_, hV j t (Pi.single k 1), rfl⟩
  have hinj : ∀ j t, Function.Injective (X.tC cr b j t) := by
    intro j t
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro c hc
    rw [tC_eq] at hc
    apply X.lin_uL_injective cr b hW (hpos.2.2 b) hI j t
    rw [map_zero]
    exact eq_zero_of_range_adjoint _ (lin_mem (hZk j t) c) hc
  have hle : ∀ j t, LinearMap.range (X.tC cr b j t) ≤ LinearMap.range (X.w0C b j) := by
    rintro j t _ ⟨c, rfl⟩
    rw [tC_eq]
    exact hDn j t (Submodule.mem_map_of_mem (lin_mem (hVk j t) c))
  have hspan : ∀ j t, Submodule.span ℂ (Set.range fun x : Fin ((lv (fc X.zs) b).dZ j t) → K =>
      X.jL j t (cr.toL X.zs b j t x)) ≤ LinearMap.range (lin (X.uL cr b j t)) := by
    intro j t
    rw [Submodule.span_le]
    rintro _ ⟨x, rfl⟩
    exact ⟨cpt Bs.v0.embedding x, (X.jL_toL cr b j t x).symm⟩
  refine ⟨fun j t => ⟨hinj j t, le_antisymm (hle j t) ?_⟩, ?_⟩
  · rw [← (hP j).2]
    refine iSup_le fun p => ?_
    intro w hw
    obtain ⟨hwp, hwr⟩ := Submodule.mem_inf.1 hw
    have h1 : LinearMap.adjoint (X.θ' j t) w ∈
        LinearMap.range (LinearMap.adjoint (X.θ' j t)) ⊓ X.goodPartComplexPoints cv b j t :=
      Submodule.mem_inf.2 ⟨⟨w, rfl⟩, hUp j t (Submodule.mem_map_of_mem hwr)⟩
    rw [← hR j t] at h1
    obtain ⟨c, hc⟩ := hspan j t h1
    have hlam := hA j t p w hw
    have hne : ((X.lam j t p Bs.v0 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (hpos.2.1 j t p Bs.v0).ne'
    refine ⟨((X.lam j t p Bs.v0 : ℝ) : ℂ)⁻¹ • c, ?_⟩
    rw [map_smul, tC_eq, hc, hlam, smul_smul, inv_mul_cancel₀ hne, one_smul]
  · intro j t p x hx y
    have hx' := hx
    rw [tC_eq, ← jL_toL] at hx'
    rw [tC_eq, tC_eq, ← jL_toL, ← jL_toL]
    have hu : X.jL j t (cr.toL X.zs b j t x) ∈ LinearMap.range (LinearMap.adjoint (X.θ' j t)) := hZ j t x
    have hw : X.θ' j t (X.jL j t (cr.toL X.zs b j t x)) ∈ X.Wp j p ⊓ LinearMap.range (X.w0C b j) := by
      refine Submodule.mem_inf.2 ⟨hx', hle j t ⟨cpt Bs.v0.embedding x, ?_⟩⟩
      rw [tC_eq, jL_toL]
    have hA' := hA j t p _ hw
    have key : LinearMap.adjoint (X.θ' j t) (X.θ' j t (X.jL j t (cr.toL X.zs b j t x))) =
        ((X.lam j t p Bs.v0 : ℝ) : ℂ) • X.jL j t (cr.toL X.zs b j t x) := by
      have hm : LinearMap.adjoint (X.θ' j t) (X.θ' j t (X.jL j t (cr.toL X.zs b j t x))) -
          ((X.lam j t p Bs.v0 : ℝ) : ℂ) • X.jL j t (cr.toL X.zs b j t x) ∈
          LinearMap.range (LinearMap.adjoint (X.θ' j t)) :=
        Submodule.sub_mem _ ⟨_, rfl⟩ (Submodule.smul_mem _ _ hu)
      have h0 : X.θ' j t (LinearMap.adjoint (X.θ' j t) (X.θ' j t (X.jL j t (cr.toL X.zs b j t x))) -
          ((X.lam j t p Bs.v0 : ℝ) : ℂ) • X.jL j t (cr.toL X.zs b j t x)) = 0 := by
        rw [map_sub, map_smul, hA', sub_self]
      exact sub_eq_zero.1 (eq_zero_of_range_adjoint _ hm h0)
    rw [← LinearMap.adjoint_inner_left, key, inner_smul_left, hI j t x y, Complex.conj_ofReal]
    push_cast
    ring

end CxData

end Formalism.IndefR.Cx
end
end

section

open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder InnerProductSpace

noncomputable section

namespace Formalism.IndefR.Cx

open Formalism.DivisionValues Formalism.L2.Indef Formalism.L2.DIV

variable {K : Type} [Field K] [NumberField K] [StarRing K]

section Dims

theorem li_cpt (σ : K →+* ℂ) {n d : ℕ} (v : Fin d → Fin n → K) (hv : LinearIndependent K v) :
    LinearIndependent ℂ (fun i => cpt σ (v i)) := by
  classical
  let M : Matrix (Fin n) (Fin d) K := Matrix.of fun r i => v i r
  have hMv : ∀ c : Fin d → K, M.mulVec c = ∑ i, c i • v i := by
    intro c; funext r
    simp [M, Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]
  have hinj : LinearMap.ker M.mulVecLin = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro c hc
    have h0 : ∑ i, c i • v i = 0 := by rw [← hMv]; exact hc
    funext i
    exact Fintype.linearIndependent_iff.1 hv c h0 i
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective M.mulVecLin hinj
  let N : Matrix (Fin d) (Fin n) K := LinearMap.toMatrix' g
  have hNM : N * M = 1 := by
    have := congrArg LinearMap.toMatrix' hg
    rw [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_id, ← Matrix.toLin'_apply', LinearMap.toMatrix'_toLin'] at this
    exact this
  have hNMc : N.map σ * M.map σ = 1 := by
    rw [← Matrix.map_mul, hNM, Matrix.map_one _ (map_zero σ) (map_one σ)]
  have hMc : ∀ c : Fin d → ℂ, (M.map σ).mulVec c = ∑ i, c i • cpt σ (v i) := by
    intro c; funext r
    simp [M, Matrix.mulVec, dotProduct, Finset.sum_apply, cpt, mul_comm]
  rw [Fintype.linearIndependent_iff]
  intro c hc i
  have h1 : (M.map σ).mulVec c = 0 := by rw [hMc]; exact hc
  have h2 : c = (N.map σ * M.map σ).mulVec c := by rw [hNMc, Matrix.one_mulVec]
  rw [← Matrix.mulVec_mulVec, h1, Matrix.mulVec_zero] at h2
  rw [h2]; rfl

theorem finrank_le_cpt {E : Type} [AddCommGroup E] [Module ℂ E] [FiniteDimensional ℂ E] (σ : K →+* ℂ) {n : ℕ}
    (L : (Fin n → ℂ) →ₗ[ℂ] E) (hL : Function.Injective L) (T : Submodule ℂ E) (S : Submodule K (Fin n → K))
    (hS : ∀ x ∈ S, L (cpt σ x) ∈ T) : finrank K S ≤ finrank ℂ (T ⊓ LinearMap.range L : Submodule ℂ E) := by
  classical
  let bs := Module.finBasis K S
  let v : Fin (finrank K S) → Fin n → K := fun i => (bs i : Fin n → K)
  have hv : LinearIndependent K v := bs.linearIndependent.map' S.subtype (Submodule.ker_subtype S)
  have hc := li_cpt σ v hv
  have hw : LinearIndependent ℂ (fun i => L (cpt σ (v i))) := hc.map' L (LinearMap.ker_eq_bot.2 hL)
  let w' : Fin (finrank K S) → (T ⊓ LinearMap.range L : Submodule ℂ E) :=
    fun i => ⟨L (cpt σ (v i)), hS _ (bs i).2, ⟨_, rfl⟩⟩
  have hw' : LinearIndependent ℂ w' := LinearIndependent.of_comp (T ⊓ LinearMap.range L).subtype hw
  simpa using hw'.fintype_card_le_finrank

variable {R V : Type} [Field R] [AddCommGroup V] [Module R V] [FiniteDimensional R V]

theorem finrank_iSup_le_sum {ι : Type} [Fintype ι] (S : ι → Submodule R V) :
    finrank R (⨆ i, S i : Submodule R V) ≤ ∑ i, finrank R (S i) := by
  classical
  have key : ∀ s : Finset ι, finrank R (⨆ i ∈ s, S i : Submodule R V) ≤ ∑ i ∈ s, finrank R (S i) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih =>
      rw [Finset.iSup_insert, Finset.sum_insert ha]
      exact (Submodule.finrank_add_le_finrank_add_finrank _ _).trans (Nat.add_le_add_left ih _)
  have hu : (⨆ i ∈ (Finset.univ : Finset ι), S i) = ⨆ i, S i := iSup_congr fun i => iSup_pos (Finset.mem_univ i)
  rw [← hu]
  exact key Finset.univ

theorem finrank_iSup_eq_sum {ι : Type} [Fintype ι] (S : ι → Submodule R V) (hS : iSupIndep S) :
    finrank R (⨆ i, S i : Submodule R V) = ∑ i, finrank R (S i) := by
  classical
  have key : ∀ s : Finset ι, finrank R (⨆ i ∈ s, S i : Submodule R V) = ∑ i ∈ s, finrank R (S i) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih =>
      rw [Finset.iSup_insert, Finset.sum_insert ha, ← ih]
      have hd : Disjoint (S a) (⨆ i ∈ s, S i) := hS.disjoint_biSup (y := (s : Set ι)) (by exact_mod_cast ha)
      have h := Submodule.finrank_sup_add_finrank_inf_eq (S a) (⨆ i ∈ s, S i)
      rw [hd.eq_bot, finrank_bot, add_zero] at h
      exact h
  have hu : (⨆ i ∈ (Finset.univ : Finset ι), S i) = ⨆ i, S i := iSup_congr fun i => iSup_pos (Finset.mem_univ i)
  rw [← hu]
  exact key Finset.univ

theorem eq_of_le_of_sum_le {ι : Type} [Fintype ι] (a c : ι → ℕ) (h : ∀ i, a i ≤ c i) (hs : ∑ i, c i ≤ ∑ i, a i) (i : ι) :
    a i = c i := by
  classical
  have hs' : ∑ i, a i = ∑ i, c i := le_antisymm (Finset.sum_le_sum fun i _ => h i) hs
  exact (Finset.sum_eq_sum_iff_of_le (fun i _ => h i)).1 hs' i (Finset.mem_univ i)

end Dims

namespace CxData

variable {Bs : DefBase K} {A : DefAmb Bs} (X : CxData A) {fc : DefSub A → DefFace Bs} (cr : Crd A fc) (b : Bool)

theorem indep_of_orth {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (T : Bs.Ix → Submodule ℂ E)
    (h : ∀ p q, p ≠ q → ∀ e ∈ T p, ∀ e' ∈ T q, ⟪e, e'⟫_ℂ = 0) : iSupIndep T := by
  apply OrthogonalFamily.independent
  rw [orthogonalFamily_iff_pairwise]
  intro p q hpq
  exact (Submodule.isOrtho_iff_inner_eq).2 (h p q hpq)

theorem finrank_Ep (hW : (lv (fc X.zs) b).WF) (h2 : X.H2 cr b) (h3 : X.H3 cr b) (hE : X.PartsE b) (p : Bs.Ix) :
    finrank K (X.Ep cr b p) = finrank ℂ (X.EEp p ⊓ X.EEl b : Submodule ℂ X.EE) := by
  have hEQ : ∀ q, X.Ep cr b q = (lv (fc X.zs) b).Qp Bs.μ0 q := by
    intro q; ext x; exact (h3 q x).symm
  have hle : ∀ q, finrank K (X.Ep cr b q) ≤ finrank ℂ (X.EEp q ⊓ X.EEl b : Submodule ℂ X.EE) := by
    intro q
    have := finrank_le_cpt Bs.v0.embedding (X.iC cr b Bs.μ0) h2.1 (X.EEp q) (X.Ep cr b q) (fun x hx => hx)
    rwa [h2.2.2] at this
  refine eq_of_le_of_sum_le _ _ hle ?_ p
  have hK : (lv (fc X.zs) b).dQ Bs.μ0 ≤ ∑ q, finrank K (X.Ep cr b q) := by
    have h := finrank_iSup_le_sum ((lv (fc X.zs) b).Qp Bs.μ0)
    rw [hW.Qp_top, finrank_top, Module.finrank_fin_fun] at h
    exact h.trans (Finset.sum_congr rfl fun q _ => by rw [hEQ q]).le
  have hC : ∑ q, finrank ℂ (X.EEp q ⊓ X.EEl b : Submodule ℂ X.EE) ≤ (lv (fc X.zs) b).dQ Bs.μ0 := by
    rw [← finrank_iSup_eq_sum _ (indep_of_orth _ hE.1)]
    calc finrank ℂ (⨆ q, X.EEp q ⊓ X.EEl b : Submodule ℂ X.EE) ≤ finrank ℂ (X.EEl b) :=
          Submodule.finrank_mono (iSup_le fun q => inf_le_right)
      _ = finrank ℂ (LinearMap.range (X.iC cr b Bs.μ0)) := by rw [h2.2.2]
      _ ≤ _ := (LinearMap.finrank_range_le _).trans (Module.finrank_fin_fun ℂ).le
  exact hC.trans hK

theorem finrank_WpK (hp : X.H4pos) (hk : X.KForm b) (he : X.EWnorm b)
    (hT : (lv (fc X.zs) b).Types) (h5 : X.H5 cr b) (hr : X.RATth cr b) (h3w : X.H3W cr b) (hPW : X.PartsW b)
    (j : Bs.J) (p : Bs.Ix) :
    finrank K (X.WpK b j p) = finrank ℂ (X.Wp j p ⊓ LinearMap.range (X.w0C b j) : Submodule ℂ (X.W j)) := by
  have hw := X.principal_form_injective b hk he (hp.2.2 b) j
  have hu : ∀ q, finrank K (X.WpK b j q) ≤
      finrank ℂ (X.Wp j q ⊓ LinearMap.range (X.w0C b j) : Submodule ℂ (X.W j)) :=
    fun q => finrank_le_cpt Bs.v0.embedding (X.w0C b j) hw (X.Wp j q) (X.WpK b j q) (fun x hx => hx)
  have hinj : Function.Injective (X.liftMat cr b j Bs.μ0).mulVecLin := by
    intro x y hxy
    apply cpt_injective Bs.v0.embedding
    apply (h5 j Bs.μ0).1
    rw [← X.key_lift cr b h5 hr, ← X.key_lift cr b h5 hr]
    exact congrArg (fun z => X.w0C b j (cpt Bs.v0.embedding z)) hxy
  have hl : ∀ q, finrank K ((lv (fc X.zs) b).Zp j Bs.μ0 q) ≤ finrank K (X.WpK b j q) := by
    intro q
    rw [LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _ hinj ((lv (fc X.zs) b).Zp j Bs.μ0 q))]
    apply Submodule.finrank_mono
    rintro _ ⟨x, hx, rfl⟩
    show X.w0C b j (cpt Bs.v0.embedding ((X.liftMat cr b j Bs.μ0).mulVec x)) ∈ X.Wp j q
    rw [X.key_lift cr b h5 hr]
    exact (h3w j q x).1 hx
  have hsum : ∀ q, finrank K ((lv (fc X.zs) b).Zp j Bs.μ0 q) =
      finrank ℂ (X.Wp j q ⊓ LinearMap.range (X.w0C b j) : Submodule ℂ (X.W j)) := by
    refine eq_of_le_of_sum_le _ _ (fun q => (hl q).trans (hu q)) ?_
    have hK : (lv (fc X.zs) b).dZ j Bs.μ0 ≤ ∑ q, finrank K ((lv (fc X.zs) b).Zp j Bs.μ0 q) := by
      have h := finrank_iSup_le_sum ((lv (fc X.zs) b).Zp j Bs.μ0)
      rwa [hT j, finrank_top, Module.finrank_fin_fun] at h
    refine le_trans ?_ hK
    rw [← finrank_iSup_eq_sum _ (indep_of_orth _ (hPW j).1)]
    calc finrank ℂ (⨆ q, X.Wp j q ⊓ LinearMap.range (X.w0C b j) : Submodule ℂ (X.W j))
          ≤ finrank ℂ (LinearMap.range (X.w0C b j)) := Submodule.finrank_mono (iSup_le fun q => inf_le_right)
      _ = finrank ℂ (LinearMap.range (X.tC cr b j Bs.μ0)) := by rw [(h5 j Bs.μ0).2]
      _ = _ := by rw [LinearMap.finrank_range_of_inj (h5 j Bs.μ0).1, Module.finrank_fin_fun]
  exact le_antisymm (hu p) ((hsum p).symm.le.trans (hl p))

theorem cutDims : X.CutDims cr b := by
  intro hW hp hk he hT h2 _ h3 h5 hr h3w hE hPW hD j p
  show finrank K (X.WpK b j p) = finrank K (X.Ep cr b p)
  rw [X.finrank_WpK cr b hp hk he hT h5 hr h3w hPW j p, hD j p, X.finrank_Ep cr b hW h2 h3 hE p]

end CxData

end Formalism.IndefR.Cx
end
end
