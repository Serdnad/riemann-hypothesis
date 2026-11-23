module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1197
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle304
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle014
public import GroundTheory.AutomorphicForms.GL2.GJMatrixAdelic
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ProductFormulaHaar.Bundle002
import GroundTheory.AutomorphicForms.Bundle012
public import GroundTheory.AutomorphicForms.StrongApproximationSLDense
import GroundTheory.GlobalFields.TateThesis.AdelicCharDual
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1214
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle149
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
import Mathlib.RingTheory.Complex
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
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
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1199
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix GlobalTheory.VacAny

noncomputable section
namespace GlobalTheory.InertVacIso

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem smul_eq_map_compFin (v : Pl (F := F)) (a : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) :
    GlobalTheory.EmbChart.atPlace v 1 • a =
      TensorProduct.map (GlobalTheory.EmbChart.atPlace v) LinearMap.id (compFin F E v a) := by
  induction a using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => rw [smul_add, hx, hy, map_add (f := _), map_add (f := _)]
  | tmul x b =>
    rw [TensorProduct.smul_tmul', smul_eq_mul, GlobalTheory.EmbChart.atPlace_mul_right, one_mul]
    simp [compFin, Algebra.TensorProduct.map_tmul]

theorem smul_eq_zero_of_compFin (v : Pl (F := F)) {a : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)} (h : compFin F E v a = 0) :
    GlobalTheory.EmbChart.atPlace v 1 • a = 0 := by
  rw [smul_eq_map_compFin, h, map_zero]

theorem compFin_cA (σ : E →ₐ[F] E) (v : Pl (F := F)) (a : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) :
    compFin F E v (cA σ a) =
      Algebra.TensorProduct.map (AlgHom.id (Fv F v) (Fv F v)) σ (compFin F E v a) := by
  induction a using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy, map_add (f := _), map_add (f := _)]
  | tmul x b => simp [cA, compFin, Algebra.TensorProduct.map_tmul]

theorem self_eq_smul_of_at {n d : ℕ} (v : Pl (F := F)) {u : Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))} (h : At (evFin F v) u) :
    u = GlobalTheory.EmbChart.atPlace v 1 • u := by
  have h1 := h (1 - GlobalTheory.EmbChart.atPlace v 1) (by rw [map_sub, map_one, GlobalTheory.EmbChart.evFin_atPlace, sub_self])
  rw [sub_smul, one_smul, sub_eq_zero] at h1
  exact h1

theorem hTens_eq_sum {α β : Type} [Fintype α] [Fintype β] (c : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E) →ₐ[AF F] _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (JA : Matrix α α (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))
    (JB : Matrix β β (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (x y : Matrix α β (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) :
    hTens c JA JB x y = ∑ i, ∑ k, JA i k * (x * JB * (y.map c)ᵀ) i k := by
  simp only [hTens, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem symp_eq_zero_of_lagAt : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {n d m : ℕ}
    (JX : Matrix (Fin n) (Fin n) E) (W : Spc F E d) (v : Pl (F := F)) (C : Matrix (Fin d) (Fin m) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))),
    GlobalTheory.InertVacLag.IsLagrAt σ W v C → ∀ (ξ : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (u u' : Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))),
    u ∈ GlobalTheory.InertVacLag.lagAt v C → u' ∈ GlobalTheory.InertVacLag.lagAt v C →
    symp (cA σ) ξ (incM F JX) (incM F W.J) u u' = 0 := by
  intro F E _ _ _ _ _ σ n d m JX W v C hL ξ u u' hu hu'
  obtain ⟨hat, z, rfl⟩ := hu
  obtain ⟨-, z', rfl⟩ := hu'
  set e := GlobalTheory.EmbChart.atPlace v (1 : Fv F v)
  set P := Cᵀ * incM F W.J * C.map (cA σ) with hP
  have hPv : P.map (compFin F E v) = 0 := by
    have h1 := hL.1
    rw [hP, Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map]
    convert h1 using 2
    · congr 1
    · ext i j
      simp only [Matrix.map_apply]
      exact compFin_cA σ v (C i j)
  have heP : e • P = 0 := by
    ext p q
    rw [Matrix.smul_apply, Matrix.zero_apply]
    apply smul_eq_zero_of_compFin
    have := congrArg (fun M => M p q) hPv
    simpa using this
  have hM : z * Cᵀ * incM F W.J * ((z' * Cᵀ).map (cA σ))ᵀ = 0 := by
    rw [self_eq_smul_of_at v hat]
    have hmap : (z' * Cᵀ).map (cA σ) = z'.map (cA σ) * Cᵀ.map (cA σ) :=
      Matrix.map_mul (f := (cA σ).toRingHom)
    rw [hmap, Matrix.transpose_mul, Matrix.transpose_map, Matrix.transpose_transpose]
    rw [Matrix.smul_mul, Matrix.smul_mul]
    have : z * Cᵀ * incM F W.J * (C.map (cA σ) * (z'.map (cA σ))ᵀ) = z * P * (z'.map (cA σ))ᵀ := by
      rw [hP]; simp only [Matrix.mul_assoc]
    rw [this, ← Matrix.smul_mul, ← Matrix.mul_smul, heP, Matrix.mul_zero, Matrix.zero_mul]
  rw [symp, hTens_eq_sum, hM]
  simp

end GlobalTheory.InertVacIso
end
end

section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

noncomputable section

namespace GlobalTheory.HoweRealKer

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {B : Base F E} {n d : ℕ} {X : Spc F E n} {W : Spc F E d} {M : Model σ X W} {om : Rep σ X W}

theorem thetaSub_ker (hA : GlobalTheory.RealActs.PolActs B M om) {P : Type} [AddCommGroup P] [Module ℂ P]
    {p : SInf F (Fin n × Fin d) →ₗ[ℂ] P} (hp : RealQuot B M om p) (hk : GlobalTheory.RealActs.KerStab B M om p) :
    GlobalTheory.Published.ThetaSubInf M B.ψ B.emb om (LinearMap.ker p ⊓ M.Pol B.ψ B.emb) := by
  obtain ⟨h1, h2, h3, h4⟩ := hA
  refine ⟨inf_le_right, ?_, ?_, ?_, ?_⟩
  · intro γ hγ f hf f₁ hf₁
    obtain ⟨D, hD, hDf⟩ := h1 γ hγ
    have e : f₁ = D f := (hDf f hf f₁).1 hf₁
    exact Submodule.mem_inf.2 ⟨LinearMap.mem_ker.2 (hp.lie γ hγ f hf f₁ hf₁), e ▸ hD f hf⟩
  · intro k hk' f hf f₁ hf₁
    obtain ⟨D, hD, hDf⟩ := h2 k hk'
    have e : f₁ = D f := (hDf f hf f₁).1 hf₁
    have hP : f₁ ∈ M.Pol B.ψ B.emb := e ▸ hD f hf
    refine Submodule.mem_inf.2 ⟨LinearMap.mem_ker.2 ?_, sub_mem hP hf⟩
    rw [map_sub, hp.cpt k hk' f hf f₁ hf₁, sub_self]
  · intro γ hγ f hf f₁ hf₁
    obtain ⟨hf0, hfP⟩ := Submodule.mem_inf.1 hf
    obtain ⟨D, hD, hDf⟩ := h3 γ hγ
    have e : f₁ = D f := (hDf f hfP f₁).1 hf₁
    exact Submodule.mem_inf.2 ⟨LinearMap.mem_ker.2 (hk.1 γ hγ f hfP f₁ hf₁ (LinearMap.mem_ker.1 hf0)), e ▸ hD f hfP⟩
  · intro k hk' f hf f₁ hf₁
    obtain ⟨hf0, hfP⟩ := Submodule.mem_inf.1 hf
    obtain ⟨D, hD, hDf⟩ := h4 k hk'
    have e : f₁ = D f := (hDf f hfP f₁).1 hf₁
    exact Submodule.mem_inf.2 ⟨LinearMap.mem_ker.2 (hk.2 k hk' f hfP f₁ hf₁ (LinearMap.mem_ker.1 hf0)), e ▸ hD f hfP⟩

theorem thetaSub_sup (hA : GlobalTheory.RealActs.PolActs B M om) {N N' : Submodule ℂ (SInf F (Fin n × Fin d))}
    (hN : GlobalTheory.Published.ThetaSubInf M B.ψ B.emb om N) (hN' : GlobalTheory.Published.ThetaSubInf M B.ψ B.emb om N') :
    GlobalTheory.Published.ThetaSubInf M B.ψ B.emb om (N ⊔ N') := by
  obtain ⟨_, _, h3, h4⟩ := hA
  refine ⟨sup_le hN.1 hN'.1, ?_, ?_, ?_, ?_⟩
  · intro γ hγ f hf f₁ hf₁
    exact Submodule.mem_sup_left (hN.2.1 γ hγ f hf f₁ hf₁)
  · intro k hk f hf f₁ hf₁
    exact Submodule.mem_sup_left (hN.2.2.1 k hk f hf f₁ hf₁)
  · intro γ hγ f hf f₁ hf₁
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hf
    obtain ⟨D, hD, hDf⟩ := h3 γ hγ
    have hyP := hN.1 hy
    have hzP := hN'.1 hz
    have e : f₁ = D (y + z) := (hDf _ (add_mem hyP hzP) f₁).1 hf₁
    rw [e, map_add (f := _)]
    exact add_mem (Submodule.mem_sup_left (hN.2.2.2.1 γ hγ y hy (D y) ((hDf y hyP (D y)).2 rfl)))
      (Submodule.mem_sup_right (hN'.2.2.2.1 γ hγ z hz (D z) ((hDf z hzP (D z)).2 rfl)))
  · intro k hk f hf f₁ hf₁
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hf
    obtain ⟨D, hD, hDf⟩ := h4 k hk
    have hyP := hN.1 hy
    have hzP := hN'.1 hz
    have e : f₁ = D (y + z) := (hDf _ (add_mem hyP hzP) f₁).1 hf₁
    rw [e, map_add (f := _)]
    exact add_mem (Submodule.mem_sup_left (hN.2.2.2.2 k hk y hy (D y) ((hDf y hyP (D y)).2 rfl)))
      (Submodule.mem_sup_right (hN'.2.2.2.2 k hk z hz (D z) ((hDf z hzP (D z)).2 rfl)))

theorem ker_ne_pol {P : Type} [AddCommGroup P] [Module ℂ P] [Nontrivial P]
    {p : SInf F (Fin n × Fin d) →ₗ[ℂ] P} (hp : RealQuot B M om p) :
    LinearMap.ker p ⊓ M.Pol B.ψ B.emb ≠ M.Pol B.ψ B.emb := by
  intro h
  obtain ⟨x, hx⟩ := exists_ne (0 : P)
  have hx' : x ∈ (M.Pol B.ψ B.emb).map p := by rw [hp.onto]; exact Submodule.mem_top
  obtain ⟨f, hf, rfl⟩ := Submodule.mem_map.1 hx'
  rw [← h] at hf
  exact hx (LinearMap.mem_ker.1 (Submodule.mem_inf.1 hf).1)

theorem le_ker_of_ge {P : Type} [AddCommGroup P] [Module ℂ P]
    {p : SInf F (Fin n × Fin d) →ₗ[ℂ] P} (hi : GlobalTheory.RealActs.Irred B M om p)
    {N : Submodule ℂ (SInf F (Fin n × Fin d))} (hN : GlobalTheory.Published.ThetaSubInf M B.ψ B.emb om N)
    (hle : LinearMap.ker p ⊓ M.Pol B.ψ B.emb ≤ N) (hne : N ≠ M.Pol B.ψ B.emb) :
    N ≤ LinearMap.ker p ⊓ M.Pol B.ψ B.emb := by
  have key : ∀ f ∈ M.Pol B.ψ B.emb, p f ∈ N.map p → f ∈ N := by
    intro f hf hpf
    obtain ⟨y, hy, hyf⟩ := Submodule.mem_map.1 hpf
    have h0 : f - y ∈ LinearMap.ker p ⊓ M.Pol B.ψ B.emb :=
      Submodule.mem_inf.2 ⟨LinearMap.mem_ker.2 (by rw [map_sub, hyf, sub_self]), sub_mem hf (hN.1 hy)⟩
    have := add_mem (hle h0) hy
    simpa using this
  rcases hi (N.map p)
      (fun γ hγ f hf f₁ hf₁ hpf => Submodule.mem_map_of_mem (hN.2.2.2.1 γ hγ f (key f hf hpf) f₁ hf₁))
      (fun k hk f hf f₁ hf₁ hpf => Submodule.mem_map_of_mem (hN.2.2.2.2 k hk f (key f hf hpf) f₁ hf₁)) with h | h
  · intro x hx
    have : p x ∈ N.map p := Submodule.mem_map_of_mem hx
    rw [h] at this
    exact Submodule.mem_inf.2 ⟨LinearMap.mem_ker.2 ((Submodule.mem_bot ℂ).1 this), hN.1 hx⟩
  · exact absurd (le_antisymm hN.1 (fun f hf => key f hf (by rw [h]; exact Submodule.mem_top))) hne

theorem ker_eq {P Q : Type} [AddCommGroup P] [Module ℂ P] [AddCommGroup Q] [Module ℂ Q] [Nontrivial P] [Nontrivial Q]
    {p : SInf F (Fin n × Fin d) →ₗ[ℂ] P} {q : SInf F (Fin n × Fin d) →ₗ[ℂ] Q}
    (hA : GlobalTheory.RealActs.PolActs B M om)
    (hH : ∀ N N', GlobalTheory.Published.ThetaSubInf M B.ψ B.emb om N → GlobalTheory.Published.ThetaSubInf M B.ψ B.emb om N' →
      N ≠ M.Pol B.ψ B.emb → N' ≠ M.Pol B.ψ B.emb → N ⊔ N' ≠ M.Pol B.ψ B.emb)
    (hp : RealQuot B M om p) (hq : RealQuot B M om q) (hkp : GlobalTheory.RealActs.KerStab B M om p)
    (hkq : GlobalTheory.RealActs.KerStab B M om q) (hip : GlobalTheory.RealActs.Irred B M om p) (hiq : GlobalTheory.RealActs.Irred B M om q) :
    LinearMap.ker p ⊓ M.Pol B.ψ B.emb = LinearMap.ker q ⊓ M.Pol B.ψ B.emb := by
  have tp := thetaSub_ker hA hp hkp
  have tq := thetaSub_ker hA hq hkq
  have hS := thetaSub_sup hA tp tq
  have hne := hH _ _ tp tq (ker_ne_pol hp) (ker_ne_pol hq)
  have h1 := le_ker_of_ge hip hS le_sup_left hne
  have h2 := le_ker_of_ge hiq hS le_sup_right hne
  exact le_antisymm (le_sup_left.trans h2) (le_sup_right.trans h1)

theorem exists_equiv : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
    (M : Model σ X W) (om : Rep σ X W) (P Q : Type) [AddCommGroup P] [Module ℂ P] [AddCommGroup Q] [Module ℂ Q] (p : SInf F (Fin n × Fin d) →ₗ[ℂ] P) (q : SInf F (Fin n × Fin d) →ₗ[ℂ] Q),
    GlobalTheory.RealActs.PolActs B M om →
    (∀ N N', GlobalTheory.Published.ThetaSubInf M B.ψ B.emb om N → GlobalTheory.Published.ThetaSubInf M B.ψ B.emb om N' → N ≠ M.Pol B.ψ B.emb → N' ≠ M.Pol B.ψ B.emb → N ⊔ N' ≠ M.Pol B.ψ B.emb) →
    RealQuot B M om p → RealQuot B M om q → Nontrivial P → Nontrivial Q → GlobalTheory.RealActs.KerStab B M om p → GlobalTheory.RealActs.KerStab B M om q →
    GlobalTheory.RealActs.Irred B M om p → GlobalTheory.RealActs.Irred B M om q → ∃ ψ : P ≃ₗ[ℂ] Q, ∀ f ∈ M.Pol B.ψ B.emb, q f = ψ (p f) := by
  intro F E _ _ _ _ _ σ B n d X W M om P Q _ _ _ _ p q hA hH hp hq hPn hQn hkp hkq hip hiq
  have hK := ker_eq hA hH hp hq hkp hkq hip hiq
  set Pol := M.Pol B.ψ B.emb
  let p' := p.domRestrict Pol
  let q' := q.domRestrict Pol
  have sp : Function.Surjective p' := by
    intro y
    have hy : y ∈ Pol.map p := by rw [hp.onto]; exact Submodule.mem_top
    obtain ⟨f, hf, rfl⟩ := Submodule.mem_map.1 hy
    exact ⟨⟨f, hf⟩, rfl⟩
  have sq : Function.Surjective q' := by
    intro y
    have hy : y ∈ Pol.map q := by rw [hq.onto]; exact Submodule.mem_top
    obtain ⟨f, hf, rfl⟩ := Submodule.mem_map.1 hy
    exact ⟨⟨f, hf⟩, rfl⟩
  have hker : LinearMap.ker p' = LinearMap.ker q' := by
    ext ⟨f, hf⟩
    simp only [p', q', LinearMap.mem_ker, LinearMap.domRestrict_apply]
    have := SetLike.ext_iff.1 hK f
    simp only [Submodule.mem_inf, LinearMap.mem_ker] at this
    constructor
    · intro h; exact (this.1 ⟨h, hf⟩).1
    · intro h; exact (this.2 ⟨h, hf⟩).1
  refine ⟨(p'.quotKerEquivOfSurjective sp).symm.trans
    ((Submodule.quotEquivOfEq _ _ hker).trans (q'.quotKerEquivOfSurjective sq)), fun f hf => ?_⟩
  have e1 : (p'.quotKerEquivOfSurjective sp).symm (p f) = Submodule.Quotient.mk ⟨f, hf⟩ := by
    rw [LinearEquiv.symm_apply_eq]; rfl
  simp only [LinearEquiv.trans_apply, e1, Submodule.quotEquivOfEq_mk]
  rfl

end GlobalTheory.HoweRealKer

end
end

section

noncomputable section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicSvN MeasureTheory
open GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open scoped Matrix

namespace GlobalTheory.AdelicSvN.Weyl

variable {F : Type} [Field F] [NumberField F]

theorem trace_eq_mixedTrace (m : mixedEmbedding.mixedSpace F) :
    Algebra.trace ℝ (mixedEmbedding.mixedSpace F) m = mixedTrace F m := by
  classical
  rw [Algebra.trace_prod_apply, PI.ProdFormulaE.Tr.trace_pi, PI.ProdFormulaE.Tr.trace_pi, mixedTrace_apply]
  simp only [Algebra.trace_complex_apply, Algebra.trace_self_apply]

theorem isStd_infinite {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) (z : InfiniteAdeleRing F) :
    ψ (infiniteAdeleInl z) = (adelicChar F (infiniteAdeleInl z) : ℂ) := by
  have hat : At (evI F) (infiniteAdeleInl z : AF F) := by
    intro u hu
    have h1 : u.1 = 0 := (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective (by rw [map_zero]; exact hu)
    refine Prod.ext ?_ ?_
    · change u.1 * _ = 0
      rw [h1, zero_mul]
    · change u.2 * 0 = 0
      rw [mul_zero]
  have h2 : adelicChar F (infiniteAdeleInl z) = Real.fourierChar (-infiniteTrace F z) := adelicChar_infinite z
  rw [hψ.2.2 _ hat, h2, trace_eq_mixedTrace, ← mixedTrace_homeomorphMixedSpace, homeomorphMixedSpace_apply,
    Real.fourierChar_apply]
  congr 1
  have : evI F (infiniteAdeleInl z) = InfiniteAdeleRing.ringEquiv_mixedSpace F z := rfl
  rw [this]
  push_cast
  ring

theorem isStd_eq {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) (a : AF F) : ψ a = (adelicChar F a : ℂ) := by
  have hfin : ∀ y : FiniteAdeleRing (𝓞 F) F,
      ψ (finiteAdeleInr y) = (adelicChar F (finiteAdeleInr y) : ℂ) := by
    intro y
    refine (GroundTheory.Automorphic.AdelicGLn.denseRange_algebraMap_finiteAdeleRing F).induction_on
      (p := fun y => ψ (finiteAdeleInr y) = (adelicChar F (finiteAdeleInr y) : ℂ)) y
      (isClosed_eq (hψ.1.comp continuous_finiteAdeleInr)
        (continuous_subtype_val.comp ((continuous_adelicChar (K := F)).comp continuous_finiteAdeleInr))) fun k => ?_
    have hs := infiniteAdeleInl_add_finiteAdeleInr (algebraMap F (AF F) k)
    rw [adeleRing_algebraMap_fst, adeleRing_algebraMap_snd] at hs
    have e : (finiteAdeleInr (algebraMap F (FiniteAdeleRing (𝓞 F) F) k) : AF F) =
        algebraMap F (AF F) k + infiniteAdeleInl (-algebraMap F (InfiniteAdeleRing F) k) := by
      rw [← hs, map_neg]; abel
    rw [e, AddChar.map_add_eq_mul, AddChar.map_add_eq_mul, hψ.2.1, adelicChar_algebraMap, one_mul, one_mul,
      isStd_infinite hψ]
  rw [← infiniteAdeleInl_add_finiteAdeleInr a, AddChar.map_add_eq_mul, AddChar.map_add_eq_mul, Circle.coe_mul,
    isStd_infinite hψ, hfin]

variable {κ : Type} [Fintype κ]

theorem pureA_eq (f : SInf F κ) (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ) :
    pureA F f g = schwartzBruhatTensorPi f g := by
  funext x
  simp only [pureA, schwartzBruhatTensorPi]
  rfl

omit [Fintype κ] in
theorem mem_SB_iff (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ) :
    g ∈ SB (κ → FiniteAdeleRing (𝓞 F) F) ↔ g ∈ finiteSchwartzBruhatPi F :=
  (mem_finiteSchwartzBruhatPi F).symm

theorem schA_eq : schA F κ = schwartzBruhatPi (K := F) (ι := κ) := by
  unfold schA schwartzBruhatPi
  congr 1

def fourierLin : schA F κ →ₗ[ℂ] (κ → AF F) → ℂ where
  toFun φ := adelicFourierPi F φ.1
  map_add' φ φ' := adelicFourierPi_add (integrable_of_mem_schwartzBruhatPi (schA_eq (F := F) (κ := κ) ▸ φ.2))
    (integrable_of_mem_schwartzBruhatPi (schA_eq (F := F) (κ := κ) ▸ φ'.2))
  map_smul' c φ := adelicFourierPi_smul c φ.1

theorem act_weyl [DecidableEq κ] (w : (κ → AF F) × (κ → AF F)) :
    act (Matrix.fromBlocks (0 : Matrix κ κ F) 1 (-1) 0) w = (w.2, -w.1) := by
  have h0 : (0 : Matrix κ κ F).map (algebraMap F (AF F)) = 0 := Matrix.map_zero _ (map_zero _)
  have h1 : (1 : Matrix κ κ F).map (algebraMap F (AF F)) = 1 := Matrix.map_one _ (map_zero _) (map_one _)
  have h2 : (-1 : Matrix κ κ F).map (algebraMap F (AF F)) = -1 := by rw [Matrix.map_neg _ (map_neg _), h1]
  simp only [act, Matrix.fromBlocks_map, h0, h1, h2, Matrix.fromBlocks_mulVec, Sum.elim_comp_inl, Sum.elim_comp_inr,
    Matrix.zero_mulVec, Matrix.one_mulVec, Matrix.neg_mulVec, zero_add, add_zero]

theorem integral_add_right_pi (f : (κ → AF F) → ℂ) (a : κ → AF F) :
    ∫ x, f (x + a) ∂(adeleMeasurePi F) = ∫ x, f x ∂(adeleMeasurePi F) := by
  let _ : MeasurableSpace (AdeleRing (𝓞 F) F) := measurableSpace_adeleRing F
  have : BorelSpace (AdeleRing (𝓞 F) F) := borelSpace_adeleRing F
  have : BorelSpace (κ → AdeleRing (𝓞 F) F) := Pi.borelSpace
  have : MeasurableAdd (κ → AdeleRing (𝓞 F) F) := ContinuousAdd.measurableAdd
  exact integral_add_right_eq_self f a

theorem fourier_schr {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) (w : (κ → AF F) × (κ → AF F)) (φ : (κ → AF F) → ℂ) :
    adelicFourierPi F (schr ψ w φ) = schr ψ (w.2, -w.1) (adelicFourierPi F φ) := by
  funext y
  simp only [adelicFourierPi, schr, ← isStd_eq hψ]
  rw [← integral_const_mul, ← integral_add_right_pi _ (-w.1)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  have h2 : ⅟(2 : AF F) + ⅟(2 : AF F) = 1 := invOf_two_add_invOf_two
  have e : ((x + -w.1) ⬝ᵥ w.2 + ⅟(2 : AF F) * (w.1 ⬝ᵥ w.2)) + (x + -w.1) ⬝ᵥ y =
      (y ⬝ᵥ -w.1 + ⅟(2 : AF F) * (w.2 ⬝ᵥ -w.1)) + x ⬝ᵥ (y + w.2) := by
    simp only [add_dotProduct, dotProduct_add, neg_dotProduct, dotProduct_neg, dotProduct_comm y w.1,
      dotProduct_comm w.2 w.1]
    linear_combination (w.1 ⬝ᵥ w.2) * h2
  have e' := congrArg ψ e
  rw [AddChar.map_add_eq_mul ψ _ ((x + -w.1) ⬝ᵥ y), AddChar.map_add_eq_mul ψ _ (x ⬝ᵥ (y + w.2))] at e'
  simp only [neg_add_cancel_right]
  change _ * _ * ψ ((x + -w.1) ⬝ᵥ y) = _ * (_ * ψ (x ⬝ᵥ (y + w.2)))
  linear_combination φ x * e'

theorem realised_weyl : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ → ∀ (κ : Type) [Fintype κ]
    [DecidableEq κ], Realised ψ (Matrix.fromBlocks (0 : Matrix κ κ F) 1 (-1) 0) := by
  intro F _ _ ψ hψ κ _ _
  have hk : ∀ φ ∈ schA F κ, adelicFourierPi F φ ∈ schA F κ := fun φ hφ => by
    rw [schA_eq] at hφ ⊢
    exact adelicFourierPi_mem_schwartzBruhatPi hφ
  have hinv : ∀ φ ∈ schA F κ, adelicFourierPi F (adelicFourierPi F φ) = fun x => φ (-x) := fun φ hφ => by
    rw [schA_eq] at hφ
    exact adelicFourierPi_adelicFourierPi hφ
  refine ⟨adelicFourierPi F, hk, fun φ hφ => ⟨_, hk _ (hk _ (hk _ hφ)), ?_⟩, fun l hl => ?_, fun w φ _ => ?_⟩
  · rw [hinv _ (hk _ (hk _ hφ)), hinv _ hφ]
    simp only [neg_neg]
  · obtain ⟨T, hT⟩ := LinearMap.exists_extend (fourierLin (F := F) (κ := κ))
    have hT' : ∀ φ ∈ schA F κ, T φ = adelicFourierPi F φ := fun φ hφ => LinearMap.congr_fun hT ⟨φ, hφ⟩
    refine ⟨l ∘ₗ T, fun g hg => ?_, fun φ hφ => by rw [LinearMap.comp_apply, hT' φ hφ]⟩
    obtain ⟨U, hU⟩ := hl (finiteFourierPi F g) ((mem_SB_iff _).2 (finiteFourierPi_mem ((mem_SB_iff g).1 hg)))
    refine ⟨U.comp (mixedFourierPiSchwartz F), fun f => ?_⟩
    rw [LinearMap.comp_apply, hT' _ (Submodule.subset_span ⟨f, g, hg, rfl⟩), ContinuousLinearMap.comp_apply, ← hU,
      pureA_eq, pureA_eq, adelicFourierPi_schwartzBruhatTensorPi]
  · rw [act_weyl, fourier_schr hψ]

end GlobalTheory.AdelicSvN.Weyl

end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.MBLow.Cl GlobalTheory.MBLow.Cl.CubHol
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.MBLow.Cl.CubHol

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} [Algebra (FractionRing R) ℂ] {N : NumD ℂ} {g : ℕ}

theorem wI_mem_chart (ν : NumOf D ℂ N) (d : AB N.toNumB g) (x y z : Fin g → ℂ) (j : thK → D.P.L.ι) (I : thK)
    (hz : ⊤ ≤ pt3 ν d x y z ⁻¹ᵁ cubW D j) :
    ⊤ ≤ (ν.eA (d.ex (wI x y z I))).left ⁻¹ᵁ D.P.L.U (j I) := by
  have h1 : ⊤ ≤ pt3 ν d x y z ⁻¹ᵁ (thφ D.P.A (x3 D.P.A) I ⁻¹ᵁ D.P.L.U (j I)) :=
    fun q hq => LB.wchart_le D.P.L (thφ D.P.A (x3 D.P.A)) j I (hz hq)
  rw [← complexCubeAbelianPoint_thetaFace_eq_partialSum ν d x y z I]
  exact fun q hq => h1 hq

theorem differentiable_wI (x y : Fin g → ℂ) (I : thK) : Differentiable ℂ (fun z => wI x y z I) := by
  unfold wI
  refine Differentiable.fun_sum fun a _ => ?_
  fin_cases a
  · exact differentiable_const _
  · exact differentiable_const _
  · exact differentiable_id

theorem frG_wI_hol_ne (ν : NumOf D ℂ N) (d : AB N.toNumB g) (geo : Geo ν d) (x y : Fin g → ℂ)
    (j : thK → D.P.L.ι) (I : thK) :
    DifferentiableOn ℂ (fun z => geo.frG (j I) (wI x y z I)) {z | ⊤ ≤ pt3 ν d x y z ⁻¹ᵁ cubW D j} ∧
      ∀ z, ⊤ ≤ pt3 ν d x y z ⁻¹ᵁ cubW D j → geo.frG (j I) (wI x y z I) ≠ 0 := by
  refine ⟨(geo.fr_hol (j I)).comp (differentiable_wI x y I).differentiableOn
    fun z hz => wI_mem_chart ν d x y z j I hz, fun z hz => ?_⟩
  set w := wI x y z I
  have hj := wI_mem_chart ν d x y z j I hz
  have hp := ν.good (ν.eA (d.ex w)).left
  have hpj : ⊤ ≤ (ν.eA (d.ex w)).left ⁻¹ᵁ (D.P.L.U (ν.J (ν.eA (d.ex w)).left) ⊓ D.P.L.U (j I)) :=
    fun q hq => ⟨hp hq, hj hq⟩
  have hc := geo.fr_compat _ (j I) w hpj
  have hne : geo.frG (ν.J (ν.eA (d.ex w)).left) w ≠ 0 := by
    rw [← geo.fr_eq w]
    exact mul_ne_zero (Units.ne_zero _) (GlobalTheory.Ex.Arch.AbVal.rg_ne_zero ν)
  rw [hc] at hne
  exact right_ne_zero_of_mul hne

end GlobalTheory.MBLow.Cl.CubHol

end
end
