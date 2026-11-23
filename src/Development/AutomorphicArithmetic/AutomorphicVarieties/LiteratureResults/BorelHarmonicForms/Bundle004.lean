module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.DerivativeRightTranslateL2
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle118
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle084
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.AbsPowOneNotIsAlgRat
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.NotIsTemperedGLDetRepTwo
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.InfinitesimalCharacterPullback.HasInfCharPullSub
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WignerHighestWeights.Bundle001
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible UpperTheory.V.Lit UpperTheory.V.Lit.Bor
open scoped TensorProduct

private theorem sum_coord_re {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (z : Cinf E) :
    ∑ τ : E →+* ℂ, coord τ z = ((2 * ∑ w : InfinitePlace E, (z w).re : ℝ) : ℂ) := by
  have h := congrArg Multiplicative.toAdd
    (GlobalTheory.GKCoh.Tests.prod_coord (M := Multiplicative ℂ) Multiplicative.ofAdd z)
  simp only [toAdd_prod, toAdd_mul, toAdd_ofAdd, Complex.add_conj] at h
  rw [h, Finset.mul_sum, Complex.ofReal_sum]

theorem UpperTheory.V.Lit.Bor.twEx :
    UpperTheory.V.Lit.Bor.TwEx := by
  intro E _ _ _ a _ r
  have hν := GlobalTheory.HeckeGal.Model.absPow_isAbsPow E (r / (2 * ((a : ℝ) * Fintype.card (InfinitePlace E))))
  refine ⟨_, ⟨_, hν⟩, fun X φ => ?_⟩
  rw [lie_mulChi, GlobalTheory.CuspRep.AlgExpo.dchi_eq_sum]
  simp only [(GlobalTheory.CuspRep.InfType.expo_of_infType E _).2.1 _ hν, ← Finset.mul_sum]
  rw [sum_coord_re, ← Complex.ofReal_mul]
  have e : ell E a X = (∑ w : InfinitePlace E, ((Matrix.of X).trace w).re) /
      ((a : ℝ) * Fintype.card (InfinitePlace E)) := by
    simp [ell, Matrix.trace]
  rw [e]
  congr 4
  ring
end

section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible UpperTheory.V.Lit UpperTheory.V.Lit.Bor
open scoped TensorProduct

private theorem emb_split {E : Type} [Field E] [_root_.NumberField.IsTotallyComplex E] (z : (E →+* ℂ) → ℂ) :
    ∃ u v : Cinf E, z = emb E u + Complex.I • emb E v := by
  refine ⟨fun w => (z w.embedding + starRingEnd ℂ (z (ComplexEmbedding.conjugate w.embedding))) / 2,
    fun w => -Complex.I * (z w.embedding - starRingEnd ℂ (z (ComplexEmbedding.conjugate w.embedding))) / 2, ?_⟩
  funext τ
  change z τ = coord τ _ + Complex.I * coord τ _
  have key : ∃ w : InfinitePlace E, τ = w.embedding ∨ τ = ComplexEmbedding.conjugate w.embedding := by
    refine ⟨InfinitePlace.mk τ, ?_⟩
    have h' : InfinitePlace.mk (InfinitePlace.mk τ).embedding = InfinitePlace.mk τ := InfinitePlace.mk_embedding _
    exact (InfinitePlace.mk_eq_iff.1 h').imp Eq.symm Eq.symm
  obtain ⟨w, rfl | rfl⟩ := key
  · rw [UpperTheory.V.FieldIso.coord_embedding, UpperTheory.V.FieldIso.coord_embedding]
    linear_combination ((z w.embedding - starRingEnd ℂ (z (ComplexEmbedding.conjugate w.embedding))) / 2) * Complex.I_mul_I
  · rw [UpperTheory.V.FieldIso.coord_conj, UpperTheory.V.FieldIso.coord_conj, UpperTheory.V.FieldIso.coord_embedding,
      UpperTheory.V.FieldIso.coord_embedding]
    simp only [map_div₀, map_add (f := _), map_sub, map_mul, map_neg, Complex.conj_I, Complex.conj_conj, map_ofNat]
    linear_combination (-(starRingEnd ℂ (z w.embedding) - z (ComplexEmbedding.conjugate w.embedding)) / 2) * Complex.I_mul_I

private theorem emb_cont {E : Type} [Field E] : Continuous (emb E) := by
  refine continuous_pi fun τ => ?_
  change Continuous (coord τ)
  unfold coord
  split_ifs
  · exact continuous_apply _
  · exact Complex.continuous_conj.comp (continuous_apply _)

open scoped Matrix.Norms.Operator in
private theorem exp_map_emb {E : Type} [Field E] [NumberField E] {a : ℕ} (Y : Matrix (Fin a) (Fin a) (Cinf E)) :
    (NormedSpace.exp Y).map (emb E) = NormedSpace.exp (Y.map (emb E)) :=
  NormedSpace.map_exp (RingHom.mapMatrix (m := Fin a) (emb E)) (continuous_id.matrix_map emb_cont) Y

open scoped Matrix.Norms.Operator in
private theorem exp_diff {T : Type} [Fintype T] {a : ℕ} (P Q : Matrix (Fin a) (Fin a) (T → ℂ)) :
    Differentiable ℂ fun s : ℂ => (fun i j => NormedSpace.exp (P + s • Q) i j : Fin a → Fin a → T → ℂ) := by
  set_option synthInstance.maxHeartbeats 200000 in
  have h : Differentiable ℂ fun s : ℂ => NormedSpace.exp (P + s • Q) := fun s =>
    (NormedSpace.exp_analytic (𝕂 := ℂ) (P + s • Q)).differentiableAt.comp s
      (f := fun s : ℂ => P + s • Q) ((differentiableAt_const P).add (differentiableAt_id.smul_const Q))
  refine differentiable_pi.2 fun i => differentiable_pi.2 fun j => ?_
  let l : Matrix (Fin a) (Fin a) (T → ℂ) →ₗ[ℂ] (T → ℂ) := Matrix.entryLinearMap ℂ (T → ℂ) i j
  exact (LinearMap.toContinuousLinearMap l).differentiable.comp h

theorem UpperTheory.V.Lit.Bor.holIdExp :
    UpperTheory.V.Lit.Bor.HolIdExp := by
  intro E _ _ _ a Φ hΦ h0 X
  choose A B hAB using fun i j => emb_split (X i j)
  let P := (Matrix.of A).map (emb E)
  let Q := (Matrix.of B).map (emb E)
  have hX : X = P + Complex.I • Q := by
    exact Matrix.ext fun i j => hAB i j
  have hd : Differentiable ℂ fun s : ℂ => Φ fun i j => NormedSpace.exp (P + s • Q) i j :=
    differentiableOn_univ.1 (hΦ.comp (exp_diff P Q).differentiableOn fun s _ => Matrix.isUnit_exp (P + s • Q))
  have hr : ∀ t : ℝ, (Φ fun i j => NormedSpace.exp (P + (t : ℂ) • Q) i j) = 0 := fun t => by
    have e : P + (t : ℂ) • Q = (Matrix.of A + t • Matrix.of B).map (emb E) := by
      ext i j τ
      change coord τ (A i j) + (t : ℂ) * coord τ (B i j) = coord τ (A i j + t • B i j)
      rw [map_add (f := _), UpperTheory.V.FieldIso.coord_smul, Complex.real_smul]
    rw [e, ← exp_map_emb]
    exact h0 (Matrix.isUnit_exp (Matrix.of A + t • Matrix.of B)).unit
  have hf : ∃ᶠ s in nhdsWithin (0 : ℂ) {0}ᶜ, (Φ fun i j => NormedSpace.exp (P + s • Q) i j) = (fun _ => 0) s := by
    have ht : Filter.Tendsto (fun t : ℝ => (t : ℂ)) (nhdsWithin 0 {0}ᶜ) (nhdsWithin 0 {0}ᶜ) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
      · simpa using (Complex.continuous_ofReal.tendsto 0).mono_left nhdsWithin_le_nhds
      · exact eventually_nhdsWithin_of_forall fun t ht => by simpa using ht
    exact ht.frequently (Filter.Frequently.of_forall hr)
  have := AnalyticOnNhd.eq_of_frequently_eq (fun s _ => hd.analyticAt s) analyticOnNhd_const hf
  rw [hX]
  exact congrFun this Complex.I
end

section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible UpperTheory.V.Lit UpperTheory.V.Lit.Bor
open scoped TensorProduct

private theorem exp_map_coord {ι : Type} [Fintype ι] {a : ℕ} (X : Matrix (Fin a) (Fin a) (ι → ℂ)) (w : ι) :
    (NormedSpace.exp X).map (fun x => x w) = NormedSpace.exp (X.map fun x => x w) := by
  classical
  have hc : Continuous fun M : Matrix (Fin a) (Fin a) (ι → ℂ) => M.map fun x => x w :=
    continuous_id.matrix_map (continuous_apply w)
  have key := open scoped Norms.Operator in
    NormedSpace.map_exp ((Pi.evalRingHom (fun _ : ι => ℂ) w).mapMatrix :
      Matrix (Fin a) (Fin a) (ι → ℂ) →+* Matrix (Fin a) (Fin a) ℂ) hc X
  exact key

private theorem gen_prod {ι : Type} [Fintype ι] {a : ℕ} (H : Submonoid (Matrix (Fin a) (Fin a) (ι → ℂ)))
    (hH : ∀ X, NormedSpace.exp X ∈ H) (y : Matrix (Fin a) (Fin a) (ι → ℂ)) (hy : IsUnit y) : y ∈ H := by
  classical
  obtain ⟨J, hJ⟩ : ∃ J : (ι → Matrix (Fin a) (Fin a) ℂ) → Matrix (Fin a) (Fin a) (ι → ℂ),
      J = fun g => Matrix.of fun i j v => g v i j := ⟨_, rfl⟩
  have Jmap : ∀ g v, (J g).map (fun x => x v) = g v := by
    intro g v
    subst hJ
    ext i j
    rfl
  have Jmul : ∀ g h, J (g * h) = J g * J h := by
    intro g h
    subst hJ
    ext i j v
    simp [Matrix.mul_apply, Finset.sum_apply]
  have Jone : J 1 = 1 := by
    subst hJ
    ext i j v
    by_cases hij : i = j
    · subst hij
      simp
    · simp [Matrix.one_apply, hij]
  have Jext : ∀ M N : Matrix (Fin a) (Fin a) (ι → ℂ),
      (∀ v, M.map (fun x => x v) = N.map (fun x => x v)) → M = N := by
    intro M N h
    ext i j v
    exact congrFun (congrFun (h v) i) j
  have single : ∀ (w : ι) (m : Matrix (Fin a) (Fin a) ℂ), m.det ≠ 0 →
      J (Function.update 1 w m) ∈ H := by
    intro w m hm
    let K : Submonoid (Matrix (Fin a) (Fin a) ℂ) :=
      { carrier := {p | J (Function.update 1 w p) ∈ H}
        one_mem' := by
          show J (Function.update 1 w 1) ∈ H
          have : Function.update (1 : ι → Matrix (Fin a) (Fin a) ℂ) w 1 = 1 := by
            funext v
            by_cases hv : v = w
            · subst hv
              simp
            · simp [hv]
          rw [this, Jone]
          exact H.one_mem
        mul_mem' := by
          intro p q hp hq
          show J (Function.update 1 w (p * q)) ∈ H
          have : Function.update (1 : ι → Matrix (Fin a) (Fin a) ℂ) w (p * q) =
              Function.update (1 : ι → Matrix (Fin a) (Fin a) ℂ) w p *
                Function.update (1 : ι → Matrix (Fin a) (Fin a) ℂ) w q := by
            funext v
            by_cases hv : v = w
            · subst hv
              simp
            · simp [hv]
          rw [this, Jmul]
          exact H.mul_mem hp hq }
    have hK : ∀ X, NormedSpace.exp X ∈ K := by
      intro X
      show J (Function.update 1 w (NormedSpace.exp X)) ∈ H
      have : J (Function.update 1 w (NormedSpace.exp X)) =
          NormedSpace.exp (J (Function.update 0 w X)) := by
        apply Jext
        intro v
        rw [Jmap, exp_map_coord, Jmap]
        by_cases hv : v = w
        · subst hv
          simp
        · simp [hv, NormedSpace.exp_zero]
      rw [this]
      exact hH _
    exact UpperTheory.V.AlgRepEndIrreducible.expGenC a K hK m hm
  have hdet : ∀ v, (y.map fun x => x v).det ≠ 0 := by
    intro v
    have h1 := hy.map (Pi.evalRingHom (fun _ : ι => ℂ) v).mapMatrix
    rw [Matrix.isUnit_iff_isUnit_det] at h1
    exact h1.ne_zero
  have all : ∀ s : Finset ι,
      J (fun v => if v ∈ s then y.map (fun x => x v) else 1) ∈ H := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      have : (fun v => if v ∈ (∅ : Finset ι) then y.map (fun x => x v) else 1) = 1 := by
        funext v
        simp
      rw [this, Jone]
      exact H.one_mem
    | insert b s hb ih =>
      have : (fun v => if v ∈ insert b s then y.map (fun x => x v) else 1) =
          Function.update (1 : ι → Matrix (Fin a) (Fin a) ℂ) b (y.map fun x => x b) *
            (fun v => if v ∈ s then y.map (fun x => x v) else 1) := by
        funext v
        by_cases hv : v = b
        · subst hv
          simp [hb]
        · simp [hv]
      rw [this, Jmul]
      exact H.mul_mem (single b _ (hdet b)) ih
  have hy' : y = J (fun v => if v ∈ (Finset.univ : Finset ι) then y.map (fun x => x v) else 1) := by
    apply Jext
    intro v
    rw [Jmap]
    simp
  rw [hy']
  exact all _

theorem UpperTheory.V.Lit.Bor.expGenPi :
    UpperTheory.V.Lit.Bor.ExpGenPi := by
  intro T _ a H hH y
  have h : y.val ∈ H.map (Units.coeHom _) := by
    refine gen_prod (ι := T) (H.map (Units.coeHom _)) ?_ y.val y.isUnit
    intro X
    obtain ⟨u, hu⟩ := Matrix.isUnit_exp X
    exact ⟨u, hH X u hu, hu⟩
  obtain ⟨u, hu, h'⟩ := h
  have : u = y := Units.ext h'
  exact this ▸ hu
end
