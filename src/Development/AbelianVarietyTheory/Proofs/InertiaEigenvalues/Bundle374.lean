module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIsLiftOfMemKO
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NontrivialOfIrreducible
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle303
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnipotentBlockColumnIndex
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExpoConjOfIsCsd
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle352
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinrankLetterHomComp
import Mathlib.Algebra.Module.StablyFree.Basic
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ContinuousCycMod
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle354
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
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.LinearAlgebra.Eigenspace.Semisimple
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AutomorphicArithmetic.IntegralCasts.Bundle001
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle014
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle015
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle012
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle016
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
import Formalism.SharpRestriction.LevelLetterCocycles.BlochKatoPhases
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc

@[expose] public section

section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead GlobalTheory.PendOf GlobalTheory.LevelType
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.EmptySecondBlock

section Reindex

variable {R : Type} [CommRing R] {t : ℕ} {c : Bool → ℕ}

def falseEquiv (f : (Σ j, Fin (c j)) ≃ Fin t) (hc : c true = 0) : Fin (c false) ≃ Fin t :=
  Equiv.ofBijective (fun i => f ⟨false, i⟩) ⟨fun i j h => by
    have := f.injective h
    simpa using this, fun x => by
    obtain ⟨⟨b, i⟩, rfl⟩ := f.surjective x
    cases b with
    | false => exact ⟨i, rfl⟩
    | true => exact absurd i.2 (by omega)⟩

theorem leviEmb_mulSingle (f : (Σ j, Fin (c j)) ≃ Fin t) (hc : c true = 0) (h : GL (Fin t) R) :
    leviEmb R f (Pi.mulSingle (M := fun j => GL (Fin (c j)) R) false (reix R (falseEquiv f hc).symm h)) = h := by
  refine Units.ext (Matrix.ext fun x y => ?_)
  obtain ⟨⟨a, i⟩, rfl⟩ := f.surjective x
  obtain ⟨⟨b, j⟩, rfl⟩ := f.surjective y
  cases a with
  | true => exact absurd i.2 (by omega)
  | false =>
    cases b with
    | true => exact absurd j.2 (by omega)
    | false =>
      rw [leviEmb_apply_same]
      simp [val_reix, falseEquiv, Equiv.ofBijective]

end Reindex

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {c : Bool → ℕ}

theorem deltaHalf_eq_one (hc : c true = 0) (g : Levi k (fun j => Fin (c j))) :
    deltaHalf k (fun j => Fin (c j)) g = 1 := by
  haveI : IsEmpty (Fin (c true)) := by rw [hc]; infer_instance
  rw [deltaHalf_apply, Fintype.prod_bool]
  have h1 : modExp (fun j => Fin (c j)) false = 0 := by
    simp only [modExp, Finset.sum_filter, Fintype.sum_bool]
    simp [hc]
  have h2 : Matrix.GeneralLinearGroup.det (g true) = 1 := by
    ext; simp [Matrix.det_isEmpty]
  have h0 : absPow k 0 = 1 := by
    ext x; simp [val_absPow]
  rw [h1, h2]
  simp [h0]

end GlobalTheory.EmptySecondBlock

end

namespace GlobalTheory.EmptySecondBlock

open GlobalTheory.SmGL.DepthZero

theorem isSubquotient_comp' {G G' V W : Type} [Group G] [Group G'] [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
    [Module ℂ W] {σ : Representation ℂ G W} {π : Representation ℂ G V} (h : IsSubquotient σ π) (ψ : G' →* G) :
    IsSubquotient (σ.comp ψ : Representation ℂ G' W) (π.comp ψ : Representation ℂ G' V) := by
  obtain ⟨S, f, hf⟩ := h
  exact ⟨⟨S.toSubmodule, fun g _ hv => S.apply_mem_toSubmodule (ψ g) hv⟩,
    ⟨f.toLinearMap, fun g => f.isIntertwining' (ψ g)⟩, hf⟩

theorem isSubquotient_of_empty_second_block : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (r : ℕ) (c : Bool → ℕ) (f : (Σ j, Fin (c j)) ≃ Fin r) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin r) F) V) (s : ∀ j, IrrRep (GL (Fin (c j)) F)), c true = 0 → IsSubquotient (piTensor fun j => (s j).ρ) (GlobalTheory.SmGL.jac f π) → ∃ φ : Fin r ≃ Fin (c false), IsSubquotient ((s false).ρ.comp (reix F φ) : Representation ℂ (GL (Fin r) F) (s false).V) π := by
  intro F _ _ _ _ r c f V _ _ π s hc hsub
  refine ⟨(falseEquiv f hc).symm, ?_⟩
  let ι : GL (Fin r) F →* Levi F (fun j => Fin (c j)) :=
    (MonoidHom.mulSingle (fun j => GL (Fin (c j)) F) false).comp (reix F (falseEquiv f hc).symm)
  have hι : ∀ h, leviEmb F f (ι h) = h := fun h => leviEmb_mulSingle f hc h

  let q : π.IntertwiningMap ((GlobalTheory.SmGL.jac f π).comp ι) :=
    ⟨(twKer π (unipRad F f) 1).mkQ, fun h => by
      ext w
      show Submodule.Quotient.mk (π h w) = GlobalTheory.SmGL.jac f π (ι h) (Submodule.Quotient.mk w)
      rw [jac_mk, deltaHalf_eq_one hc, inv_one, Units.val_one, one_smul, hι]⟩
  have h3 : IsSubquotient ((GlobalTheory.SmGL.jac f π).comp ι) π :=
    IsSubquotient.of_surjective q (Submodule.mkQ_surjective _)
  have h2 := isSubquotient_comp' hsub ι

  haveI := nontrivial_of_irreducible (s true).irr
  obtain ⟨w0, hw0⟩ := exists_ne (0 : (s true).V)
  obtain ⟨ψ0, hψ0⟩ : ∃ ψ0 : Module.Dual ℂ (s true).V, ψ0 w0 ≠ 0 := by
    by_contra h
    push_neg at h
    exact hw0 ((Module.forall_dual_apply_eq_zero_iff ℂ w0).1 h)
  let ψ : ∀ j, (s j).V →ₗ[ℂ] ℂ := fun j => Bool.rec (motive := fun j => (s j).V →ₗ[ℂ] ℂ) 0 ((ψ0 w0)⁻¹ • ψ0) j
  let K : Representation.IntertwiningMap ((piTensor fun j => (s j).ρ).comp ι : Representation ℂ (GL (Fin r) F) _)
      ((s false).ρ.comp (reix F (falseEquiv f hc).symm) : Representation ℂ (GL (Fin r) F) _) :=
    ⟨contract ψ false, fun h => by
      refine LinearMap.ext fun t => ?_
      exact contract_piTensor (fun j => (s j).ρ) ψ false (reix F (falseEquiv f hc).symm h) t⟩
  have hK : Function.Surjective K := fun y => by
    let x : ∀ j, (s j).V := fun j => Bool.rec (motive := fun j => (s j).V) y w0 j
    refine ⟨PiTensorProduct.tprod ℂ x, ?_⟩
    show contract ψ false (PiTensorProduct.tprod ℂ x) = y
    rw [contract_tprod]
    have : Finset.univ.erase false = {true} := by decide
    rw [this, Finset.prod_singleton]
    show ((ψ0 w0)⁻¹ • ψ0) w0 • y = y
    rw [LinearMap.smul_apply, smul_eq_mul, inv_mul_cancel₀ hψ0, one_smul]
  exact (IsSubquotient.of_surjective K hK).trans (h2.trans h3)

end GlobalTheory.EmptySecondBlock
end

section

noncomputable section

open NumberField Matrix GlobalTheory.CuspRep MeasureTheory

namespace GlobalTheory.CuspGeneric

def cuspBlockIndexEquivLastColumnIndex (a r : ℕ) : BlockIx a r ≃ UnipotentBlockColumnIndex a r (a - 1) where
  toFun p := ⟨p.1, p.2.1, p.2.2, by have := p.1.2.isLt; omega⟩
  invFun q := ⟨q.1, q.2.1, q.2.2.1⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem posM_apply_of_blkIx {R : Type} [CommRing R] {a r m : ℕ} (x : UnipotentBlockColumnIndex a r m → R) (i j : Fin a) :
    posM Subtype.val x i j = if h : (i : ℕ) < r ∧ r ≤ (j : ℕ) ∧ (j : ℕ) ≤ m then x ⟨(i, j), h⟩ else 0 := by
  classical
  simp only [posM, Matrix.sum_apply]
  split_ifs with h
  · rw [Finset.sum_eq_single ⟨(i, j), h⟩]
    · simp [Matrix.single_apply]
    · intro t _ ht
      rw [Matrix.single_apply, if_neg]
      rintro ⟨h1, h2⟩
      exact ht (Subtype.ext (Prod.ext h1 h2))
    · simp
  · refine Finset.sum_eq_zero fun t _ => ?_
    rw [Matrix.single_apply, if_neg]
    rintro ⟨h1, h2⟩
    have := t.2
    rw [h1, h2] at this
    exact h this

theorem blkU_eq_unip {R : Type} [CommRing R] {a r : ℕ} (x : UnipotentBlockColumnIndex a r (a - 1) → R) :
    (blkU x : GL (Fin a) R) = unip (fun p => x (cuspBlockIndexEquivLastColumnIndex a r p)) := by
  apply Units.ext
  ext i j
  change (1 + posM Subtype.val x : Matrix (Fin a) (Fin a) R) i j = (1 + nilM _ : Matrix (Fin a) (Fin a) R) i j
  rw [Matrix.add_apply, Matrix.add_apply, posM_apply_of_blkIx]
  simp only [nilM, Matrix.of_apply]
  congr 1
  have hj := j.2
  by_cases h : (i : ℕ) < r ∧ r ≤ (j : ℕ)
  · rw [dite_eq_left h, dite_eq_left ⟨h.1, h.2, by omega⟩]
    rfl
  · rw [dite_eq_right h, dite_eq_right (fun h' => h ⟨h'.1, h'.2.1⟩)]

theorem avg_blk_last_eq_zero : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (F : GA E a → ℂ),
    Continuous F → (∀ (γ : GL (Fin a) E) (g : GA E a), F (ratGL E a γ * g) = F g) → GlobalTheory.CuspRep.IsCuspidal F →
    ∀ r : ℕ, 0 < r → r ≤ a - 1 → ∀ g : GA E a,
      GlobalTheory.CuspGeneric.avg (GlobalTheory.CuspGeneric.ratV E (GlobalTheory.CuspGeneric.UnipotentBlockColumnIndex a r (a - 1)))
        (fun x => F ((GlobalTheory.CuspGeneric.blkU x : GA E a) * g)) = 0 := by
  intro E _ _ _ a F _ _ hF r hr0 hr g
  have hra : r < a := by omega
  letI : MeasurableSpace (UnipotentBlockColumnIndex a r (a - 1) → Ad E) := borel _
  haveI : BorelSpace (UnipotentBlockColumnIndex a r (a - 1) → Ad E) := ⟨rfl⟩
  letI : MeasurableSpace (BlockIx a r → Ad E) := borel _
  haveI : BorelSpace (BlockIx a r → Ad E) := ⟨rfl⟩
  simp only [avg]
  split_ifs with h
  swap
  · rfl
  obtain ⟨hμ, h𝓕, -⟩ := h.choose_spec
  set μ := h.choose.1
  set 𝓕 := h.choose.2
  let e := cuspBlockIndexEquivLastColumnIndex a r
  let β : (UnipotentBlockColumnIndex a r (a - 1) → Ad E) ≃ₜ+ (BlockIx a r → Ad E) :=
    { toFun := fun x p => x (e p)
      invFun := fun y q => y (e.symm q)
      left_inv := fun x => funext fun q => congrArg x (e.apply_symm_apply q)
      right_inv := fun y => funext fun p => congrArg y (e.symm_apply_apply p)
      map_add' := fun _ _ => rfl
      continuous_toFun := continuous_pi fun p => continuous_apply (e p)
      continuous_invFun := continuous_pi fun q => continuous_apply (e.symm q) }
  let q : ratN E a r ≃ ratV E (UnipotentBlockColumnIndex a r (a - 1)) :=
    { toFun := fun y => ⟨β.symm y, by
        obtain ⟨c, hc⟩ := y.2
        exact ⟨fun t => c (e.symm t), by rw [← hc]; rfl⟩⟩
      invFun := fun x => ⟨β x, by
        obtain ⟨c, hc⟩ := x.2
        exact ⟨fun p => c (e p), by rw [← hc]; rfl⟩⟩
      left_inv := fun y => Subtype.ext (β.apply_symm_apply y)
      right_inv := fun x => Subtype.ext (β.symm_apply_apply x) }
  let m := β.toHomeomorph.toMeasurableEquiv
  have h2 := hF r hr0 hra (μ.map m) (m '' 𝓕) (β.isAddHaarMeasure_map μ)
    (h𝓕.image_of_equiv m.toEquiv (MeasurePreserving.symm m ⟨m.measurable, rfl⟩).quasiMeasurePreserving q fun y x => by
      change β (β.symm y + x) = y + β x
      rw [map_add (f := _), β.apply_symm_apply]) g
  rw [m.measurableEmbedding.setIntegral_map, m.injective.preimage_image] at h2
  rw [← h2]
  congr 1
  funext x
  rw [blkU_eq_unip]
  rfl

end GlobalTheory.CuspGeneric
end
end

section

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.CuspGeneric

namespace GlobalTheory.CuspGeneric

theorem IsMir.succ {E : Type} [Field E] {a m : ℕ} {γ : GL (Fin a) E} (hγ : IsMir m γ) : IsMir (m + 1) γ :=
  fun i k h => hγ i k (by omega)

theorem colT_isMir_invariant : ∀ (E : Type) [Field E] [NumberField E] (a : ℕ) (ψ : AddChar (Ad E) ℂ), StdPsi ψ →
    ∀ (m : ℕ) (f : GA E a → ℂ), m + 1 < a → Good ψ (m + 1) f → ∀ γ : GL (Fin a) E, IsMir m γ →
    ∀ g, colT ψ (m + 1) f (ratGL E a γ * g) = colT ψ (m + 1) f g := by
  intro E _ _ a ψ hψ m f hma hf γ hγ g
  have key := GlobalTheory.T.whittakerCoefficient_rationalMirabolic_mul E a ψ hψ m f hf.cont hf.left γ hγ.succ (eLast a (m + 1)) g
  unfold colT
  rw [key]
  congr 1
  funext t
  let s0 : UnipotentBlockColumnIndex a (m + 1) (m + 1) := ⟨(⟨m, by omega⟩, ⟨m + 1, hma⟩), Nat.lt_succ_self m, le_refl _, le_refl _⟩
  rw [Finset.sum_eq_single s0]
  · have h1 : eLast (E := E) a (m + 1) s0 = 1 := by simp [eLast, s0]
    rw [h1, one_mul, hγ _ _ (Or.inl (le_refl m))]
    have ht := t.2.1
    simp only [eLast, Matrix.one_apply]
    by_cases h : (t.1.1 : ℕ) = m
    · rw [if_pos (Fin.ext h.symm), if_pos (by omega)]
    · rw [if_neg (fun e => h (congrArg Fin.val e).symm), if_neg (by omega)]
  · intro s _ hs
    have h0 : eLast (E := E) a (m + 1) s = 0 := by
      simp only [eLast]
      rw [if_neg]
      intro e
      apply hs
      have h2 := s.2.2
      apply Subtype.ext
      exact Prod.ext (Fin.ext (by simp [s0]; omega)) (Fin.ext (by simp [s0]; omega))
    rw [h0, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

end GlobalTheory.CuspGeneric
end
end

section

noncomputable section

open Polynomial Module

namespace GlobalTheory.LetterSep

theorem eq_zero_of_forall_letterHom {L U D F k : Type} [Field L] [Field U] [AddCommGroup D] [Module L D]
    (m : U →+* Module.End L D) [Field F] [Field k] [Algebra k L] [Algebra k U] [Algebra k F]
    [Algebra U F] [IsScalarTower k U F] [IsAlgClosed F] [FiniteDimensional k L]
    [Algebra.IsSeparable k L] [Module U D] [FiniteDimensional U D]
    (hm : ∀ (c : U) (x : D), c • x = m c x)
    (hk : ∀ (c : k) (x : D), m (algebraMap k U c) x = algebraMap k L c • x) (x : D)
    (hx : ∀ s : L →ₐ[k] F, ∀ f ∈ GlobalTheory.Pst.LetterDim.letterHom m (s : L →+* F) (algebraMap U F),
      f x = 0) :
    x = 0 := by
  classical
  let sm : L → D →ₗ[U] D := fun a =>
    { toFun := fun x => a • x, map_add' := smul_add a
      map_smul' := fun c x => by rw [hm, RingHom.id_apply, hm, map_smul] }
  let r : L →+* Module.End F (D →ₗ[U] F) :=
    { toFun := fun a =>
        { toFun := fun f => f ∘ₗ sm a, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
      map_one' := by ext f x; simp [sm]
      map_mul' := fun a b => by ext f x; simp [sm, smul_smul, mul_comm]
      map_zero' := by ext f x; simp [sm]
      map_add' := fun a b => by ext f x; simp [sm, add_smul] }
  have hr : ∀ a f y, r a f y = f (a • y) := fun _ _ _ => rfl
  have hrk : ∀ c : k, r (algebraMap k L c) =
      algebraMap F (Module.End F (D →ₗ[U] F)) (algebraMap k F c) := fun c => by
    ext f y
    rw [hr, ← hk, ← hm, map_smul, Module.algebraMap_end_apply, LinearMap.smul_apply, Algebra.smul_def,
      ← IsScalarTower.algebraMap_apply, smul_eq_mul]
  obtain ⟨α, hα⟩ := Field.exists_primitive_element k L
  have hint : IsIntegral k α := Algebra.IsIntegral.isIntegral α
  have hpoly : ∀ a : L, ∃ q : k[X], a = aeval α q := fun a => by
    have : a ∈ (IntermediateField.adjoin k {α}).toSubalgebra := by rw [hα]; trivial
    rw [IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint.isAlgebraic,
      Algebra.adjoin_singleton_eq_range_aeval] at this
    obtain ⟨q, hq⟩ := this
    exact ⟨q, hq.symm⟩
  have hev : ∀ q : k[X], r (aeval α q) = aeval (r α) (q.map (algebraMap k F)) := fun q => by
    rw [aeval_def, aeval_def, hom_eval₂, eval₂_map]
    congr 1
    exact RingHom.ext hrk
  have hE : ∀ s : L →ₐ[k] F, (⨅ a, (r a).eigenspace (s a)) = (r α).eigenspace (s α) := fun s => by
    refine le_antisymm (iInf_le _ α) (le_iInf fun a y hy => ?_)
    obtain ⟨q, rfl⟩ := hpoly a
    rw [End.mem_eigenspace_iff] at hy ⊢
    rw [hev, End.aeval_apply_of_mem_apply_eq_smul hy, eval_map_algebraMap, aeval_algHom_apply]
  have h0 : aeval (r α) ((minpoly k α).map (algebraMap k F)) = 0 := by
    rw [← hev, minpoly.aeval, map_zero]
  have hss : (r α).IsSemisimple := End.isSemisimple_of_squarefree_aeval_eq_zero
    (Polynomial.Separable.map (Algebra.IsSeparable.isSeparable k α)).squarefree h0
  have htop : ⊤ ≤ ⨆ s : L →ₐ[k] F, ⨅ a, (r a).eigenspace (s a) := by
    rw [← hss.iSup_eigenspace_eq_top]
    refine iSup_le fun μ y hy => ?_
    rcases eq_or_ne y 0 with rfl | hy0
    · exact zero_mem _
    have h1 := End.aeval_apply_of_mem_apply_eq_smul (p := (minpoly k α).map (algebraMap k F))
      (End.mem_eigenspace_iff.mp hy)
    rw [h0, LinearMap.zero_apply, eq_comm, smul_eq_zero_iff_left hy0, eval_map_algebraMap] at h1
    have h2 : μ ∈ Set.range fun s : L →ₐ[k] F => s α := by
      rw [Algebra.IsAlgebraic.range_eval_eq_rootSet_minpoly F α, mem_rootSet]
      exact ⟨minpoly.ne_zero hint, h1⟩
    obtain ⟨s, rfl⟩ := h2
    exact Submodule.mem_iSup_of_mem s (by rw [hE s]; exact hy)
  by_contra hx0
  obtain ⟨φ, hφ⟩ : ∃ φ : Module.Dual U D, φ x ≠ 0 := by
    by_contra h
    push_neg at h
    exact hx0 ((Module.forall_dual_apply_eq_zero_iff U x).mp h)
  let f : D →ₗ[U] F := (Algebra.linearMap U F) ∘ₗ φ
  have hf : f x ≠ 0 := by
    simp only [f, LinearMap.comp_apply, Algebra.linearMap_apply]
    exact (_root_.map_ne_zero _).mpr hφ
  apply hf
  refine Submodule.iSup_induction (motive := fun g : D →ₗ[U] F => g x = 0) _ (htop (Submodule.mem_top (x := f)))
    (fun s g hg => ?_) rfl (fun g h hg hh => by simp [hg, hh])
  have h1 : ∀ a y, g (a • y) = s a * g y := by
    intro a y
    have := (Submodule.mem_iInf _).mp hg a
    rw [End.mem_eigenspace_iff] at this
    have := LinearMap.congr_fun this y
    simpa [hr] using this
  have h2 : ∀ c y, g (m c y) = algebraMap U F c * g y := by
    intro c y
    rw [← hm, g.map_smul, Algebra.smul_def]
  exact hx s g.toAddMonoidHom ⟨h1, h2⟩

end GlobalTheory.LetterSep
end
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.StepTwo

namespace GlobalTheory.TameRead

open GlobalTheory.TameQuot

theorem eq_one_of_mem_proKer {I M : Type} [Group I] [TopologicalSpace I] [IsTopologicalGroup I]
    [CompactSpace I] [AddCommGroup M] {l : ℕ} [Fact l.Prime] {k : ℕ}
    (hM : ∀ m : M, (l ^ k) • m = 0) (θ : I →* Multiplicative M)
    (ho : IsOpen (θ.ker : Set I)) {σ : I} (hσ : σ ∈ proKer l I) : θ σ = 1 := by
  refine mem_proKer.1 hσ θ.ker inferInstance ho ?_
  have := Subgroup.quotient_finite_of_isOpen _ ho
  refine IsPGroup.iff_card.1 fun x => ⟨k, ?_⟩
  obtain ⟨τ, rfl⟩ := QuotientGroup.mk_surjective x
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, MonoidHom.mem_ker, map_pow]
  exact hM (θ τ).toAdd

theorem exists_gen_read : TameQuotient → ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 F)), IsPlaceOver A v → ((l : ℕ) : 𝓞 F) ∉ v.asIdeal → ∃ γ ∈ Ine (F := F) A, ∀ (R : Type) [CommRing R] (M : Type) [AddCommGroup M] [Module R M] [TopologicalSpace M] [DiscreteTopology M] (rho : Representation R (G F Ω) M) (k : ℕ), (∀ m : M, (l ^ k) • m = 0) → normV v ≡ 1 [MOD l ^ k] → (∀ σ ∈ Ine (F := F) A, ∀ m, rho σ m = m) → ∀ z : Z1 rho, (z.1 γ = 0 → ∀ σ ∈ Ine (F := F) A, z.1 σ = 0) ∧ ∀ φ : G F Ω, IsFrob A (normV v) φ → rho φ (z.1 γ) = z.1 γ := by
  intro hT F Ω _ _ _ _ _ l _ A v hA hl
  obtain ⟨-, -, -, -, ⟨γ, hγ⟩, hrel⟩ := hT F Ω l A v hA hl
  refine ⟨γ, hγ.1, ?_⟩
  intro R _ M _ _ _ _ rho k hM hq hI z
  have : CompactSpace (Ine (F := F) A) := isCompact_iff_compactSpace.1 (isClosed_Ine A).isCompact
  let θ : Ine (F := F) A →* Multiplicative M :=
    MonoidHom.mk' (fun g => Multiplicative.ofAdd (z.1 g)) fun g h => by
      have := z.2.2 (g : G F Ω) h
      rw [hI _ g.2] at this
      exact congrArg Multiplicative.ofAdd this
  have ho : IsOpen (θ.ker : Set (Ine (F := F) A)) :=
    (isOpen_discrete {0}).preimage (z.2.1.comp continuous_subtype_val)
  have hJ : ∀ σ ∈ ineKer F A l, z.1 σ = 0 := fun σ hσ =>
    eq_one_of_mem_proKer hM θ ho (σ := ⟨σ, ineKer_le_Ine A l hσ⟩) (coe_mem_ineKer.1 hσ)
  refine ⟨fun h0 σ hσ => ?_, fun φ hφ => ?_⟩
  · have hc : IsClosed ((θ.ker.map (Ine (F := F) A).subtype : Subgroup (G F Ω)) : Set (G F Ω)) :=
      (isClosed_Ine A).isClosedEmbedding_subtypeVal.isClosedMap _ (θ.ker.isClosed_of_isOpen ho)
    have h1 : Subgroup.zpowers γ ⊔ ineKer F A l ≤ θ.ker.map (Ine (F := F) A).subtype :=
      sup_le (Subgroup.zpowers_le.2 ⟨⟨γ, hγ.1⟩, h0, rfl⟩) fun τ hτ =>
        ⟨⟨τ, ineKer_le_Ine A l hτ⟩, hJ τ hτ, rfl⟩
    obtain ⟨τ, hτ, rfl⟩ := Subgroup.topologicalClosure_minimal _ h1 hc (hγ.2 hσ)
    exact hτ
  · have hc : φ * γ * φ⁻¹ ∈ Ine (F := F) A := conj_mem_Ine hφ.1 hγ.1
    have h1 := hJ _ (hrel ⟨φ, hφ.1⟩ ⟨γ, Ine_le_Dec A hγ.1⟩ hφ hγ).2.1
    have h2 : θ (((⟨γ, hγ.1⟩ : Ine (F := F) A) ^ normV v)⁻¹ * ⟨_, hc⟩) = 1 := h1
    rw [map_mul, map_inv, map_pow, inv_mul_eq_one] at h2
    have h3 : normV v • z.1 γ = z.1 (φ * γ * φ⁻¹) := congrArg Multiplicative.toAdd h2
    have h4 : normV v • z.1 γ = z.1 γ := by
      rw [← Nat.mod_add_div (normV v) (l ^ k), add_smul, mul_smul, hM, add_zero, hq]
      conv_rhs => rw [← one_smul ℕ (z.1 γ), ← Nat.mod_add_div 1 (l ^ k), add_smul, mul_smul, hM,
        add_zero]
    have h5 := z.2.2 (φ * γ * φ⁻¹) φ
    rw [hI _ hc, inv_mul_cancel_right, z.2.2 φ γ, ← h3, h4, add_comm] at h5
    exact add_right_cancel h5

end GlobalTheory.TameRead
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel

theorem _root_.GlobalTheory.T.tame_local_relation_dualNumber_cocycle : TameQuotient → ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (M : ℕ) (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 F)), IsPlaceOver A v → ((l : ℕ) : 𝓞 F) ∉ v.asIdeal → 1 ≤ M → normV v % (2 * l ^ M) = 1 → ∀ d : G F Ω →* Multiplicative (ZMod (l ^ M)), IsOpen (d.ker : Set (G F Ω)) → (∀ c, ∃ σ ∈ Ine (F := F) A, d σ = c) → ∀ φ : G F Ω, IsFrob A (normV v) φ → ∃ γ ∈ Ine (F := F) A, d γ = Multiplicative.ofAdd 1 ∧ ∀ (K : Type) [Field K] [CharP K l] (W : Type) [AddCommGroup W] [Module K W] (z0 : G F Ω → W), IsLocallyConstant z0 → (∀ g ∈ Dec (F := F) A, ∀ h ∈ Dec (F := F) A, z0 (g * h) = z0 g + z0 h) → (z0 γ = 0 → ∀ σ ∈ Ine (F := F) A, z0 σ = 0) ∧ ∀ (lam : G F Ω → K) (z1 : G F Ω → W), IsLocallyConstant lam → IsLocallyConstant z1 → (∀ g ∈ Dec (F := F) A, ∀ h ∈ Dec (F := F) A, lam (g * h) = lam g + lam h) → (∀ g ∈ Dec (F := F) A, ∀ h ∈ Dec (F := F) A, z1 (g * h) = z1 g + z1 h + lam g • z0 h) → lam γ • z0 φ = lam φ • z0 γ := by
  first | exact @GlobalTheory.TameRel.tame_relation | exact GlobalTheory.TameRel.tame_relation | (intros; apply GlobalTheory.TameRel.tame_relation <;> assumption)
end
