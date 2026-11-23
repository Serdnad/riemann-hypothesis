module

public import Formalism.LocalRingCardinality.DataTheta
public import Mathlib.RepresentationTheory.Character
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RepresentationTheory.Maschke
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle011
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle010

@[expose] public section

section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible

namespace GlobalTheory.CasimirNumber

def sqSum (l : List ℚ) : ℚ := (l.map fun x => x ^ 2).sum

theorem sqSum_append (l₁ l₂ : List ℚ) : sqSum (l₁ ++ l₂) = sqSum l₁ + sqSum l₂ := by
  unfold sqSum
  rw [List.map_append, List.sum_append]

theorem sum_range_getD_sq (l : List ℚ) :
    ∑ i ∈ Finset.range l.length, (l.getD i 0) ^ 2 = sqSum l := by
  induction l with
  | nil => simp [sqSum]
  | cons a l ih =>
    rw [List.length_cons, Finset.sum_range_succ']
    simp only [List.getD_cons_succ, List.getD_cons_zero]
    rw [ih]
    unfold sqSum
    simp only [List.map_cons, List.sum_cons]
    ring

theorem sum_fin_getD_sq (l : List ℚ) (p : ℕ) (h : l.length = p) :
    ∑ i : Fin p, (l.getD i 0) ^ 2 = sqSum l := by
  subst h
  rw [Fin.sum_univ_eq_sum_range (fun i => (l.getD i 0) ^ 2)]
  exact sum_range_getD_sq l

theorem normSq_ofBlocks {p q : ℕ} (l₁ l₂ : List ℚ) (h₁ : l₁.length = p) (h₂ : l₂.length = q) :
    normSq (ofBlocks (p := p) (q := q) l₁ l₂) = sqSum l₁ + sqSum l₂ := by
  unfold normSq ofBlocks
  rw [Fintype.sum_sum_type]
  simp only
  rw [sum_fin_getD_sq l₁ p h₁, sum_fin_getD_sq l₂ q h₂]

theorem sum_range_sub_sq (c : ℚ) (n : ℕ) :
    ∑ i ∈ Finset.range n, (c - (i : ℚ)) ^ 2 =
      n * c ^ 2 - c * (n * (n - 1)) + (n - 1) * n * (2 * n - 1) / 6 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    ring

theorem rhoSq_eq (n : ℕ) : rhoSq n = (n : ℚ) * ((n : ℚ) ^ 2 - 1) / 12 := by
  unfold rhoSq
  rw [sum_range_sub_sq]
  ring

theorem length_block (t : ℕ) : (Formalism.BasicNotions.TH.block t).length = t := by
  unfold Formalism.BasicNotions.TH.block
  simp

theorem sqSum_map_range (f : ℕ → ℚ) (n : ℕ) :
    sqSum ((List.range n).map f) = ∑ i ∈ Finset.range n, f i ^ 2 := by
  induction n with
  | zero => simp [sqSum]
  | succ n ih =>
    rw [List.range_succ, List.map_append, sqSum_append, ih, Finset.sum_range_succ]
    simp [sqSum]

theorem sqSum_block (t : ℕ) : sqSum (Formalism.BasicNotions.TH.block t) = rhoSq t := by
  have hb : Formalism.BasicNotions.TH.block t = (List.range t).map (fun m : ℕ => ((t : ℚ) - 1) / 2 - m) := by
    have hf : ∀ l : List ℕ, List.flatMap (fun a : ℕ => [(Nat.cast a : ℚ)]) l = List.map (fun a : ℕ => (Nat.cast a : ℚ)) l := by
      intro l
      induction l with
      | nil => rfl
      | cons a l ih => simp [List.flatMap_cons, ih]
    unfold Formalism.BasicNotions.TH.block
    simp only [List.bind_eq_flatMap, List.pure_def]
    rw [hf, List.map_map]
    rfl
  rw [hb, sqSum_map_range]
  unfold rhoSq
  rfl

theorem normSq_lamA (al be ga de : List ℚ) :
    normSq (lamA al be ga de) = sqSum al + sqSum be + sqSum ga + sqSum de := by
  unfold lamA
  rw [normSq_ofBlocks _ _ (by simp) (by simp), sqSum_append, sqSum_append]
  ring

theorem normSq_lamA' (t : ℕ) (al be ga de : List ℚ) :
    normSq (lamA' t al be ga de) = sqSum al + sqSum be + sqSum ga + sqSum de + rhoSq t := by
  unfold lamA'
  rw [normSq_ofBlocks _ _ (by simp [length_block] <;> omega) (by simp <;> omega)]
  simp only [sqSum_append, sqSum_block]
  ring

theorem normSq_lamM' (t : ℕ) (al be ga de : List ℚ) :
    normSq (lamM' t al be ga de) = sqSum al + sqSum be + sqSum ga + sqSum de + rhoSq t := by
  unfold lamM'
  rw [normSq_ofBlocks _ _ (by simp <;> omega) (by simp [length_block] <;> omega)]
  simp only [sqSum_append, sqSum_block]
  ring

theorem casimir_number_identity : ∀ (t : ℕ) (al be ga de : List ℚ), HypA t al be ga de → normSq (lamA' t al be ga de) - rhoSq (al.length + be.length + ga.length + de.length + t) = normSq (lamA al be ga de) - rhoSq (al.length + be.length + ga.length + de.length) - ((al.length + be.length + ga.length + de.length : ℕ) : ℚ) * ((al.length + be.length + ga.length + de.length + t : ℕ) : ℚ) * (t : ℚ) / 4 ∧ normSq (lamM' t al be ga de) = normSq (lamA' t al be ga de) := by
  intro t al be ga de _
  refine ⟨?_, by rw [normSq_lamM', normSq_lamA']⟩
  rw [normSq_lamA', normSq_lamA, rhoSq_eq, rhoSq_eq, rhoSq_eq]
  push_cast
  ring

end GlobalTheory.CasimirNumber
end

section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg
open Matrix

namespace GlobalTheory.AdjDescent

theorem jm_mul_jm (p q : ℕ) : Jm p q * Jm p q = 1 := by
  unfold Jm Formalism.UG.Jpq
  rw [Matrix.fromBlocks_multiply]
  simp [Matrix.fromBlocks_one]

theorem jm_conjTranspose (p q : ℕ) : (Jm p q)ᴴ = Jm p q := by
  unfold Jm Formalism.UG.Jpq
  simp [Matrix.fromBlocks_conjTranspose]

theorem conjR_conjTranspose_mul {p q : ℕ} (Z : Mat p q) : (conjR Z)ᴴ * Jm p q = -(Jm p q * Z) := by
  unfold conjR adjZ
  rw [Matrix.conjTranspose_neg, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, jm_conjTranspose, Matrix.neg_mul, Matrix.mul_assoc,
    Matrix.mul_assoc, jm_mul_jm, Matrix.mul_one]

theorem mul_conjR {p q : ℕ} (Z : Mat p q) : Jm p q * conjR Z = -(Zᴴ * Jm p q) := by
  unfold conjR adjZ
  rw [Matrix.mul_neg, ← Matrix.mul_assoc, ← Matrix.mul_assoc, jm_mul_jm, Matrix.one_mul]

theorem re_mem_upq {p q : ℕ} (Z : Mat p q) : Z + conjR Z ∈ upq p q := by
  show (Z + conjR Z)ᴴ * Jm p q + Jm p q * (Z + conjR Z) = 0
  rw [Matrix.conjTranspose_add, Matrix.add_mul, Matrix.mul_add, conjR_conjTranspose_mul, mul_conjR]
  abel

theorem im_mem_upq {p q : ℕ} (Z : Mat p q) : Complex.I • (Z - conjR Z) ∈ upq p q := by
  show (Complex.I • (Z - conjR Z))ᴴ * Jm p q + Jm p q * (Complex.I • (Z - conjR Z)) = 0
  have hI : (star Complex.I : ℂ) = -Complex.I := Complex.conj_I
  rw [Matrix.conjTranspose_smul, hI, Matrix.conjTranspose_sub, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.sub_mul, Matrix.mul_sub, conjR_conjTranspose_mul, mul_conjR]
  simp only [neg_smul, sub_neg_eq_add, smul_add]
  abel

theorem decomp {p q : ℕ} (Z : Mat p q) :
    Z = (1 / 2 : ℂ) • (Z + conjR Z) + (-Complex.I / 2) • (Complex.I • (Z - conjR Z)) := by
  have h : (-Complex.I / 2) • (Complex.I • (Z - conjR Z)) = (1 / 2 : ℂ) • (Z - conjR Z) := by
    rw [smul_smul]
    congr 1
    rw [div_mul_eq_mul_div, neg_mul, Complex.I_mul_I]
    norm_num
  rw [h, ← smul_add, show Z + conjR Z + (Z - conjR Z) = (2 : ℂ) • Z by rw [two_smul]; abel,
    smul_smul]
  norm_num

theorem inner_apply_of_norm {G H : Type} [Group G] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (ρ : G →* (H →L[ℂ] H)) (h : ∀ g x, ‖ρ g x‖ = ‖x‖) (g : G) (x y : H) :
    inner ℂ x (ρ g y) = inner ℂ (ρ g⁻¹ x) y := by
  have e : ρ g * ρ g⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel, map_one]
  have hinv : ρ g (ρ g⁻¹ x) = x := by
    calc ρ g (ρ g⁻¹ x) = (ρ g * ρ g⁻¹) x := rfl
      _ = x := by rw [e]; rfl
  let L : H →ₗᵢ[ℂ] H := ⟨(ρ g : H →ₗ[ℂ] H), h g⟩
  calc inner ℂ x (ρ g y) = inner ℂ (L (ρ g⁻¹ x)) (L y) := by
        show inner ℂ x (ρ g y) = inner ℂ (ρ g (ρ g⁻¹ x)) (ρ g y)
        rw [hinv]
    _ = inner ℂ (ρ g⁻¹ x) y := L.inner_map_map _ _

private theorem kFin_map_of_intertwining {p q : ℕ} (T : GrpData p q) {E F : Type} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    (πE : T.G → (E →L[ℂ] E)) (πF : T.G → (F →L[ℂ] F)) (L : E →L[ℂ] F)
    (hL : ∀ g x, L (πE g x) = πF g (L x)) (x : E) (hx : KFin T πE x) : KFin T πF (L x) := by
  unfold KFin at hx ⊢
  have key : ∀ (κ : Type) (c : κ → T.G),
      FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k => πE (c k) x)) →
      FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k => πF (c k) (L x))) := by
    intro κ c hc
    have e : (Set.range fun k => πF (c k) (L x)) =
        (L : E →ₗ[ℂ] F) '' Set.range (fun k => πE (c k) x) := by
      rw [← Set.range_comp]
      congr 1
      funext k
      simp [hL]
    rw [e, Submodule.span_image]
    haveI := hc
    infer_instance
  exact key _ _ hx

theorem adjoint_descends : ∀ (p q : ℕ) (T : GrpData p q) (D : DSRep T) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (ρ : T.G →* (H →L[ℂ] H)), (∀ g x, ‖ρ g x‖ = ‖x‖) → ∀ S : D.U.H →L[ℂ] H, (∀ g x, ρ g (S x) = S (D.U.π g x)) → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (ι : V →ₗ[ℂ] H) (act : Mat p q →ₗ[ℂ] Module.End ℂ V), (∀ P, KFin T (fun g => ρ g) (ι P)) → (∀ Y ∈ upq p q, ∀ P, HasDerivAt (fun t : ℝ => ρ (T.expt (t • Y)) (ι P)) (ι (act Y P)) 0) → ∃ φ : V →ₗ[ℂ] D.HK.V, (∀ P x, inner ℂ x (D.ι (φ P)) = inner ℂ (S x) (ι P)) ∧ ∀ Z P, φ (act Z P) = D.HK.act Z (φ P) := by
  intro p q T D H _ _ _ ρ hρ S hS V _ _ ι act hK hD

  have hA : ∀ g y, ContinuousLinearMap.adjoint S (ρ g y) =
      D.U.π g (ContinuousLinearMap.adjoint S y) := by
    intro g y
    apply ext_inner_left ℂ
    intro v
    rw [ContinuousLinearMap.adjoint_inner_right, inner_apply_of_norm ρ hρ, hS,
      ← ContinuousLinearMap.adjoint_inner_right S, inner_apply_of_norm D.U.π D.U.isom]

  have hmem : ∀ P, ∃ w, D.ι w = ContinuousLinearMap.adjoint S (ι P) := fun P =>
    (D.ι_range _).2 (kFin_map_of_intertwining T (fun g => ρ g) (fun g => D.U.π g) _ hA (ι P) (hK P))
  choose f hf using hmem
  have hinj := D.ι_inj
  let φ : V →ₗ[ℂ] D.HK.V :=
    { toFun := f
      map_add' := fun P Q => hinj (by simp only [map_add (f := _), hf])
      map_smul' := fun c P => hinj (by simp only [RingHom.id_apply, map_smul, hf]) }
  have hφ : ∀ P, D.ι (φ P) = ContinuousLinearMap.adjoint S (ι P) := hf

  have hY : ∀ Y ∈ upq p q, ∀ P, φ (act Y P) = D.HK.act Y (φ P) := by
    intro Y hYm P
    apply hinj
    rw [hφ]
    have h1 : HasDerivAt (fun t : ℝ => D.U.π (T.expt (t • Y)) (D.ι (φ P)))
        (ContinuousLinearMap.adjoint S (ι (act Y P))) 0 := by
      have h0 := ((ContinuousLinearMap.adjoint S).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt
        (0 : ℝ) (hD Y hYm P)
      convert h0 using 1
      all_goals first
        | rfl
        | (funext t; simp [hA, hφ])
    exact h1.unique (D.der Y hYm (φ P))
  refine ⟨φ, fun P x => ?_, fun Z P => ?_⟩
  · rw [hφ, ContinuousLinearMap.adjoint_inner_right]
  · have hre := re_mem_upq Z
    have him := im_mem_upq Z
    rw [decomp Z]
    generalize Z + conjR Z = A at hre ⊢
    generalize Complex.I • (Z - conjR Z) = B at him ⊢
    simp only [map_add (f := _), map_smul, LinearMap.add_apply, LinearMap.smul_apply, hY A hre, hY B him]

end GlobalTheory.AdjDescent
end

section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible

noncomputable section

namespace GlobalTheory.GKQuot

variable {p q : ℕ}

def quotAct (M : GKMod p q) (N : Submodule ℂ M.V) (hN : ∀ Z, N ≤ N.comap (M.act Z)) :
    Mat p q →ₗ[ℂ] Module.End ℂ (M.V ⧸ N) where
  toFun Z := N.mapQ N (M.act Z) (hN Z)
  map_add' Z W := by
    apply Submodule.linearMap_qext
    ext x
    simp
  map_smul' c Z := by
    apply Submodule.linearMap_qext
    ext x
    simp

theorem quotAct_mk (M : GKMod p q) (N : Submodule ℂ M.V) (hN : ∀ Z, N ≤ N.comap (M.act Z))
    (Z : Mat p q) (x : M.V) : quotAct M N hN Z (N.mkQ x) = N.mkQ (M.act Z x) := rfl

def quotMod (M : GKMod p q) (N : Submodule ℂ M.V) (hN : ∀ Z, N ≤ N.comap (M.act Z)) :
    GKMod p q where
  V := M.V ⧸ N
  act := quotAct M N hN
  lie X Y := by
    refine LinearMap.ext fun v => ?_
    obtain ⟨x, rfl⟩ := N.mkQ_surjective v
    rw [quotAct_mk, M.lie X Y]
    simp only [LinearMap.sub_apply, Module.End.mul_apply, quotAct_mk, map_sub]
  kfin v := by
    obtain ⟨x, rfl⟩ := N.mkQ_surjective v
    obtain ⟨W, hW, hx, hK⟩ := M.kfin x
    refine ⟨W.map N.mkQ, inferInstance, Submodule.mem_map_of_mem hx, ?_⟩
    rintro X hX _ ⟨w, hw, rfl⟩
    rw [quotAct_mk]
    exact Submodule.mem_map_of_mem (hK X hX w hw)
  wts v := by
    obtain ⟨x, rfl⟩ := N.mkQ_surjective v
    have h : (⨆ μ : Ix p q → ℚ, wtSub M.act μ) ≤
        (⨆ μ : Ix p q → ℚ, wtSub (quotAct M N hN) μ).comap N.mkQ := by
      refine iSup_le fun μ y hy => ?_
      rw [Submodule.mem_comap]
      refine Submodule.mem_iSup_of_mem μ ?_
      simp only [wtSub, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
        LinearMap.smul_apply, LinearMap.id_apply] at hy ⊢
      intro a
      rw [quotAct_mk, ← map_smul, ← map_sub, hy a, map_zero]
    exact h (M.wts x)

theorem exists_unitary_quotient (p q : ℕ) (M : GKMod p q) (H : Type) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (E : M.V →ₗ[ℂ] H)
    (hE : ∀ Z x y, inner ℂ (E (M.act Z x)) (E y) = inner ℂ (E x) (E (M.act (adjZ Z) y))) :
    ∃ (A : UGKMod p q) (f : M.V →ₗ[ℂ] A.M.V) (Eb : A.M.V →ₗ[ℂ] H), Function.Surjective f ∧
      Function.Injective Eb ∧ (∀ x, Eb (f x) = E x) ∧ ∀ Z x, f (M.act Z x) = A.M.act Z (f x) := by

  let N : Submodule ℂ M.V := LinearMap.ker E
  have hN : ∀ Z, N ≤ N.comap (M.act Z) := by
    intro Z x hx
    have hx' : E x = 0 := hx
    show E (M.act Z x) = 0
    have h := hE Z x (M.act Z x)
    rw [hx', inner_zero_left] at h
    exact inner_self_eq_zero.mp h

  let Eb : M.V ⧸ N →ₗ[ℂ] H := N.liftQ E le_rfl
  have hEb : ∀ x, Eb (N.mkQ x) = E x := fun x => N.liftQ_apply E x
  have hinj : Function.Injective Eb := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro v hv
    obtain ⟨x, rfl⟩ := N.mkQ_surjective v
    rw [LinearMap.mem_ker, hEb] at hv
    rw [Submodule.mem_bot, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact LinearMap.mem_ker.mpr hv
  have hact : ∀ Z x, quotAct M N hN Z (N.mkQ x) = N.mkQ (M.act Z x) := quotAct_mk M N hN

  let ip : M.V ⧸ N →ₗ⋆[ℂ] M.V ⧸ N →ₗ[ℂ] ℂ := ((innerₛₗ ℂ).comp Eb).compl₂ Eb
  let A : UGKMod p q :=
    { M := quotMod M N hN
      ip := ip
      herm := by
        intro v w
        show star (inner ℂ (Eb v) (Eb w)) = inner ℂ (Eb w) (Eb v)
        exact inner_conj_symm (Eb w) (Eb v)
      pos := by
        intro v hv
        have hne : Eb v ≠ 0 := fun h0 => hv (hinj (h0.trans (map_zero Eb).symm))
        have h : 0 < RCLike.re (inner ℂ (Eb v) (Eb v)) := by
          rw [inner_self_eq_norm_sq]
          exact pow_pos (norm_pos_iff.mpr hne) 2
        show 0 < (inner ℂ (Eb v) (Eb v)).re
        exact h
      adj := by
        intro Z v w
        obtain ⟨x, rfl⟩ := N.mkQ_surjective v
        obtain ⟨y, rfl⟩ := N.mkQ_surjective w
        show inner ℂ (Eb (quotAct M N hN Z (N.mkQ x))) (Eb (N.mkQ y)) =
          inner ℂ (Eb (N.mkQ x)) (Eb (quotAct M N hN (adjZ Z) (N.mkQ y)))
        rw [hact, hact, hEb, hEb, hEb, hEb]
        exact hE Z x y }
  exact ⟨A, N.mkQ, Eb, N.mkQ_surjective, hinj, hEb, fun Z x => (hact Z x).symm⟩

end GlobalTheory.GKQuot
end
end

section

open GlobalTheory.GLq Polynomial
open scoped Classical

namespace GlobalTheory.AbsIrrDescent

theorem isSimpleModule_of_finrank_end {k R M : Type} [Field k] [Ring R] [Algebra k R] [AddCommGroup M] [Module R M]
    [Module k M] [IsScalarTower k R M] [SMulCommClass R k M] [IsSemisimpleModule R M]
    (h : Module.finrank k (Module.End R M) = 1) : IsSimpleModule R M := by
  have hE : Nontrivial (Module.End R M) := Module.nontrivial_of_finrank_eq_succ h
  have hM : Nontrivial M := by
    by_contra hM
    rw [not_nontrivial_iff_subsingleton] at hM
    exact not_subsingleton (Module.End R M) inferInstance
  have : Nontrivial (Submodule R M) := (Submodule.nontrivial_iff R).2 hM
  refine { eq_bot_or_eq_top := fun U => ?_ }
  obtain ⟨U', hU⟩ := exists_isCompl U
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' (1 : Module.End R M) one_ne_zero).1 h
    (U.subtype ∘ₗ U.projectionOnto U' hU)
  by_cases h0 : c = 0
  · left
    rw [Submodule.eq_bot_iff]
    intro x hx
    have := LinearMap.congr_fun hc x
    rw [h0, zero_smul] at this
    have h2 : (U.subtype ∘ₗ U.projectionOnto U' hU) x = x := by
      simpa using congrArg Subtype.val (Submodule.projectionOnto_apply_left hU ⟨x, hx⟩)
    rw [← h2, ← this]; rfl
  · right
    rw [Submodule.eq_top_iff']
    intro x
    have := LinearMap.congr_fun hc (c⁻¹ • x)
    have h2 : (c • (1 : Module.End R M)) (c⁻¹ • x) = x := by
      simp [smul_smul, h0]
    rw [← h2, this]
    exact Subtype.property _

theorem isIrreducible_of_norm_one {k G V : Type} [Field k] [CharZero k] [Group G] [Fintype G] [AddCommGroup V]
    [Module k V] [FiniteDimensional k V] (ρ : Representation k G V)
    (hn : ∑ g, ρ.character g * ρ.character g⁻¹ = (Nat.card G : k)) : ρ.IsIrreducible := by
  have hc : (Nat.card G : k) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  have := invertibleOfNonzero hc
  have : NeZero (Nat.card G : k) := ⟨hc⟩
  have h := Representation.card_inv_mul_sum_char_mul_char_eq_finrank ρ ρ
  rw [hn, inv_mul_cancel₀ hc, eq_comm, Nat.cast_eq_one] at h
  rw [Representation.irreducible_iff_isSimpleModule_asModule]
  refine isSimpleModule_of_finrank_end (k := k) ?_
  rw [← h]
  exact (Representation.IntertwiningMap.equivAlgEnd (ρ := ρ)).toLinearEquiv.finrank_eq.symm

end GlobalTheory.AbsIrrDescent
end
