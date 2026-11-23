module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle978
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1724
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CenterEnvelopingAlgebraDirectSum
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1796
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1791
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle029
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle367
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle491
import Formalism.HermitianLattices.HermitianLatticesProofs.LocBasic
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle154
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsTypeIsRealConst
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1793
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1689
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1646
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle052
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle045
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.BaseNorm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1792

@[expose] public section

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.SmoothForms GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies
open scoped TensorProduct

namespace GlobalTheory.CentralOps

attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance 100] LieRing.ofAssociativeRing

theorem polyFun_mem (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D)
    (R : RealPoints θ V) (P : PolyE V) : polyFun θ V P ∈ SmF θ V := GlobalTheory.T.polyFun_mem_smooth_vectors D θ V R P

theorem lieDer_polyFun (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D)
    (R : RealPoints θ V) (τ : D.what₂.Tau) (X : LieAt V τ) (P : PolyE V) :
    lieDer V (expInf θ V) (atPlace V τ X) (polyFun θ V P) = polyFun θ V (matDer τ X.1 P) := GlobalTheory.T.rightLieDerivative_realEntryPolynomialFunction D θ V R τ X P


open Classical in
theorem aeval_matDer_single {T : Type} {n : ℕ} (τ τ' : T) (a b c d : Fin n) :
    MvPolynomial.aeval (fun p : T × Fin n × Fin n => if p.2.1 = p.2.2 then (1 : ℂ) else 0)
      (matDer τ (Matrix.single a b (1 : ℂ)) (MvPolynomial.X (τ', c, d) -
        MvPolynomial.C (if c = d then (1 : ℂ) else 0))) = if (τ, a, b) = (τ', c, d) then 1 else 0 := by
  rw [map_sub, MvPolynomial.derivation_C, sub_zero, matDer_X]
  by_cases h : τ' = τ
  · subst h

    simp only [ite_true, map_sum, map_mul, MvPolynomial.aeval_X, MvPolynomial.aeval_C, Matrix.single_apply,
    Algebra.algebraMap_self, RingHom.id_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ,
    ite_true, Prod.mk.injEq, true_and]
  · simp only [h, ite_false, map_zero]
    rw [ite_eq_right]; intro h'; exact h (congrArg Prod.fst h').symm

variable {D : D7} {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} {V : HSp D}

theorem polyFun_add (P Q : PolyE V) : polyFun θ V (P + Q) = polyFun θ V P + polyFun θ V Q := by
  funext g; simp [polyFun]

theorem polyFun_smul (c : ℂ) (P : PolyE V) : polyFun θ V (c • P) = c • polyFun θ V P := by
  funext g; simp [polyFun, MvPolynomial.smul_eval]

open Classical in
theorem envRepAll_ι_of (R : RealPoints θ V) (τ : D.what₂.Tau) (y : ℂ ⊗[ℝ] LieAt V τ) :
    envRepAll R (UniversalEnvelopingAlgebra.ι ℂ (DirectSum.of (fun τ => ℂ ⊗[ℝ] LieAt V τ) τ y)) =
      envRep R τ (UniversalEnvelopingAlgebra.ι ℂ y) := by
  rw [← envIncl_ι, envRepAll_envIncl]

theorem envRepAll_polyFun (R : RealPoints θ V) (u : GlobalTheory.AutFinLit.Env V) (P : PolyE V) :
    (envRepAll R u ⟨polyFun θ V P, polyFun_mem D θ V R P⟩).1 = polyFun θ V (polyRep V u P) := by
  classical
  let S : Subalgebra ℂ (GlobalTheory.AutFinLit.Env V) :=
    { carrier := {u | ∀ P, (envRepAll R u ⟨polyFun θ V P, polyFun_mem D θ V R P⟩).1 = polyFun θ V (polyRep V u P)}
      mul_mem' := fun {u v} hu hv P => by
        rw [map_mul, map_mul, mul_apply_eq_comp, mul_apply_eq_comp, ← hu]
        congr 2
        exact Subtype.ext (hv P)
      add_mem' := fun {u v} hu hv P => by
        rw [map_add (f := _), map_add (f := _), LinearMap.add_apply, LinearMap.add_apply, Submodule.coe_add, hu, hv, polyFun_add]
      algebraMap_mem' := fun c P => by
        rw [AlgHom.commutes, AlgHom.commutes, Module.algebraMap_end_apply, Module.algebraMap_end_apply,
          Submodule.coe_smul, polyFun_smul] }
  have hι : ∀ x, UniversalEnvelopingAlgebra.ι ℂ x ∈ S := by
    intro x
    induction x using DirectSum.induction_on with
    | zero => rw [map_zero]; exact S.zero_mem
    | add x y hx hy => rw [map_add (f := _)]; exact S.add_mem hx hy
    | of τ y =>
      induction y using TensorProduct.inductionOn with
      | add y y' hy hy' => rw [map_add (f := _), map_add (f := _)]; exact S.add_mem hy hy'
      | tmul c X =>
        intro P
        rw [envRepAll_ι_of, polyRep_ι_of, placeRep_tmul,
          show c ⊗ₜ[ℝ] X = c • ((1 : ℂ) ⊗ₜ[ℝ] X) by rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one], map_smul,
          map_smul, envRep_ι, LinearMap.smul_apply, LinearMap.smul_apply, Submodule.coe_smul, opInf_coe,
          polyFun_smul, lieDer_polyFun D θ V R]
        rfl
  exact GlobalTheory.EnvCentre.mem_of_ι_mem (AlgHom.id ℂ _) S hι u P

theorem realEntries_one (R : RealPoints θ V) :
    realEntries θ V 1 = fun p => if p.2.1 = p.2.2 then (1 : ℂ) else 0 := by
  funext p
  simp only [realEntries, R.2.2.2.2.1 1 (one_mem _) p.1, Matrix.one_apply]



open Classical in
theorem envRepAll_injective (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (_hθ : IsInfFam θ)
    (V : HSp D) (R : RealPoints θ V) : Function.Injective (envRepAll R) := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro u hu
  let ρ : ∀ τ, LieAt V τ → GlobalTheory.AutFinLit.Env V := fun τ X =>
    UniversalEnvelopingAlgebra.ι ℂ (DirectSum.of (fun τ => ℂ ⊗[ℝ] LieAt V τ) τ ((1 : ℂ) ⊗ₜ[ℝ] X))
  have hadd : ∀ τ (X Y : LieAt V τ), ρ τ (X + Y) = ρ τ X + ρ τ Y := fun τ X Y => by
    simp only [ρ, TensorProduct.tmul_add, map_add (f := _)]
  have hsmul : ∀ τ (c : ℝ) (X : LieAt V τ), ρ τ (c • X) = (c : ℂ) • ρ τ X := fun τ c X => by
    have e1 : (1 : ℂ) ⊗ₜ[ℝ] (c • X) = (c : ℂ) • ((1 : ℂ) ⊗ₜ[ℝ] X) := by
      rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul', TensorProduct.smul_tmul', smul_eq_mul, mul_one,
        Complex.real_smul, mul_one]
    simp only [ρ]
    rw [e1, ← DirectSum.lof_eq_of ℂ, map_smul, map_smul, DirectSum.lof_eq_of]
  have hbrk : ∀ τ (X Y Z : LieAt V τ), Z.1 = X.1 * Y.1 - Y.1 * X.1 → ρ τ Z = ρ τ X * ρ τ Y - ρ τ Y * ρ τ X :=
    fun τ X Y Z hZ => by
      have : Z = ⁅X, Y⁆ := Subtype.ext hZ
      simp only [ρ]
      rw [this, ← Ring.lie_def, ← LieHom.map_lie, DirectSum.lie_of_same, LieAlgebra.ExtendScalars.bracket_tmul, one_mul]
  choose P Q hPQ hrest using fun τ =>
    GlobalTheory.UnitaryLieComplexification.glRel_and_span V.rank (gramAt D V τ) (R.1 τ).1 (R.1 τ).2
  have hgl := fun τ => (hrest τ (GlobalTheory.AutFinLit.Env V) (ρ τ) (hadd τ) (hsmul τ) (hbrk τ)).1
  have hsp := fun τ => (hrest τ (GlobalTheory.AutFinLit.Env V) (ρ τ) (hadd τ) (hsmul τ) (hbrk τ)).2
  let e : D.what₂.Tau × Fin V.rank × Fin V.rank → GlobalTheory.AutFinLit.Env V := fun p =>
    ρ p.1 (P p.1 p.2.1 p.2.2) + Complex.I • ρ p.1 (Q p.1 p.2.1 p.2.2)
  have hρe : ∀ τ X, ρ τ X ∈ Submodule.span ℂ (Set.range e) := fun τ X =>
    Submodule.span_mono (by rintro _ ⟨p, rfl⟩; exact ⟨(τ, p.1, p.2), rfl⟩) (hsp τ X)

  have hgen : Algebra.adjoin ℂ (Set.range e) = ⊤ := by
    refine eq_top_iff.2 ((GlobalTheory.EnvCentre.adjoin_range_ι_eq_top _).symm.le.trans (Algebra.adjoin_le ?_))
    rintro _ ⟨x, rfl⟩
    refine Algebra.span_le_adjoin ℂ _ ?_
    induction x using DirectSum.induction_on with
    | zero => rw [map_zero]; exact zero_mem _
    | add x y hx hy => rw [map_add (f := _)]; exact add_mem hx hy
    | of τ y =>
      induction y using TensorProduct.inductionOn with
      | add y y' hy hy' => rw [map_add (f := _), map_add (f := _)]; exact add_mem hy hy'
      | tmul c X =>
        rw [show c ⊗ₜ[ℝ] X = c • ((1 : ℂ) ⊗ₜ[ℝ] X) by rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one],
          ← DirectSum.lof_eq_of ℂ, map_smul, map_smul]
        exact Submodule.smul_mem _ c (hρe τ X)

  have hcomm : ∀ τ τ', τ ≠ τ' → ∀ X Y, Commute (ρ τ X) (ρ τ' Y) := fun τ τ' h X Y => by
    have h1 : ρ τ X * ρ τ' Y - ρ τ' Y * ρ τ X = 0 := by
      simp only [ρ]; rw [← Ring.lie_def, ← LieHom.map_lie, DirectSum.lie_of, dite_eq_right h, map_zero]
    exact sub_eq_zero.1 h1
  have hbr : ∀ p q, e p * e q - e q * e p ∈ Submodule.span ℂ (Set.range e) := by
    rintro ⟨τ, a, b⟩ ⟨τ', c, d⟩
    by_cases h : τ = τ'
    · subst h
      have := hgl τ a b c d
      simp only at this
      change (ρ τ (P τ a b) + Complex.I • ρ τ (Q τ a b)) * (ρ τ (P τ c d) + Complex.I • ρ τ (Q τ c d)) -
        (ρ τ (P τ c d) + Complex.I • ρ τ (Q τ c d)) * (ρ τ (P τ a b) + Complex.I • ρ τ (Q τ a b)) ∈ _
      rw [this]
      refine sub_mem ?_ ?_
      · split_ifs
        · exact Submodule.subset_span ⟨(τ, a, d), rfl⟩
        · exact zero_mem _
      · split_ifs
        · exact Submodule.subset_span ⟨(τ, c, b), rfl⟩
        · exact zero_mem _
    · have hc : Commute (e (τ, a, b)) (e (τ', c, d)) := by
        simp only [e]
        refine Commute.add_left (Commute.add_right ?_ ?_) (Commute.add_right ?_ ?_)
        · exact hcomm τ τ' h _ _
        · exact (hcomm τ τ' h _ _).smul_right _
        · exact (hcomm τ τ' h _ _).smul_left _
        · exact ((hcomm τ τ' h _ _).smul_left _).smul_right _
      rw [hc.eq, sub_self]; exact zero_mem _

  have hπρ : ∀ τ (X : LieAt V τ), polyRep V (ρ τ X) = (matDer τ X.1 : Module.End ℂ (PolyE V)) := fun τ X => by
    simp only [ρ]; rw [polyRep_ι_of, placeRep_ι]
  have hE : ∀ τ a b, (P τ a b).1 + Complex.I • (Q τ a b).1 = Matrix.single a b (1 : ℂ) := fun τ a b => by
    rw [(hPQ τ a b).1, (hPQ τ a b).2, smul_smul]
    have : Complex.I * (1 / (2 * Complex.I)) = 1 / 2 := by field_simp
    rw [this]
    module
  have hπe : ∀ p, polyRep V (e p) = (matDer p.1 (Matrix.single p.2.1 p.2.2 (1 : ℂ)) : Module.End ℂ (PolyE V)) :=
    fun p => by
      simp only [e]
      rw [map_add (f := _), map_smul, hπρ, hπρ, ← hE, matDer_add, matDer_smul]
      rfl
  have hder : ∀ p (x y : PolyE V), polyRep V (e p) (x * y) = polyRep V (e p) x * y + x * polyRep V (e p) y :=
    fun p x y => by
      rw [hπe]
      change matDer _ _ (x * y) = matDer _ _ x * y + x * matDer _ _ y
      rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]; ring
  let pt : D.what₂.Tau × Fin V.rank × Fin V.rank → ℂ := fun p => if p.2.1 = p.2.2 then (1 : ℂ) else 0
  let χ : PolyE V →ₐ[ℂ] ℂ := MvPolynomial.aeval pt
  let a : D.what₂.Tau × Fin V.rank × Fin V.rank → PolyE V := fun p => MvPolynomial.X p - MvPolynomial.C (pt p)
  have ha0 : ∀ k, χ (a k) = 0 := fun k => by simp [χ, a]
  have hδ : ∀ i k, χ (polyRep V (e i) (a k)) = if i = k then 1 else 0 := by
    rintro ⟨τ, a', b'⟩ ⟨τ', c, d⟩
    rw [hπe]
    exact aeval_matDer_single τ τ' a' b' c d
  refine GlobalTheory.T.faithful_of_derivations_dualFamily _ _ _ e hgen hbr (polyRep V) hder χ a ha0 hδ u fun x => ?_
  have h1 := congrFun (envRepAll_polyFun R u x) 1
  rw [hu, LinearMap.zero_apply, ZeroMemClass.coe_zero, Pi.zero_apply] at h1
  have h2 : polyFun θ V (polyRep V u x) 1 = χ (polyRep V u x) := by
    rw [polyFun, realEntries_one R, MvPolynomial.aeval_eq_eval₂Hom, Algebra.algebraMap_self]; rfl
  rw [← h2, ← h1]

end GlobalTheory.CentralOps
end
end

section

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Datum Formalism.IndefR.Lev
open GlobalTheory.FormTies GlobalTheory.OnTies GlobalTheory.TraceClassRank
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OnCmp GlobalTheory.BigOn GlobalTheory.RealIndexBound

namespace GlobalTheory.OnRankAlg

section Gen

variable {K : Type} [Field K] [NumberField K]
variable {Z : Type} [AddCommGroup Z] [Module K Z] [Module (𝓞 K) Z] [IsScalarTower (𝓞 K) K Z]

theorem exists_smul_mem_of_mem_span {A : Submodule (𝓞 K) Z} {x : Z} (hx : x ∈ Submodule.span K (A : Set Z)) :
    ∃ d : 𝓞 K, d ≠ 0 ∧ d • x ∈ A := by
  first
  | exact @_root_.GlobalTheory.TargetLemmaCollection.target
  | exact _root_.GlobalTheory.TargetLemmaCollection.target
  | (apply _root_.GlobalTheory.TargetLemmaCollection.target <;> assumption)
  | (intros; apply _root_.GlobalTheory.TargetLemmaCollection.target <;> assumption)
  | (intros; apply @_root_.GlobalTheory.TargetLemmaCollection.target <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.TargetLemmaCollection.target ..)

theorem span_cut {A : Submodule (𝓞 K) Z} (hA : Submodule.span K (A : Set Z) = ⊤) (W : Submodule K Z) :
    Submodule.span K (Formalism.EigenvalueLevelCeiling.cut W A : Set Z) = W := by
  apply le_antisymm
  · rw [Submodule.span_le]
    intro x hx
    exact (Submodule.mem_inf.1 hx).2
  · intro w hw
    obtain ⟨d, hd, hm⟩ := exists_smul_mem_of_mem_span (A := A) (x := w) (by rw [hA]; trivial)
    have hd' : algebraMap (𝓞 K) K d ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).2 hd
    have hmem : d • w ∈ Formalism.EigenvalueLevelCeiling.cut W A := by
      refine Submodule.mem_inf.2 ⟨hm, ?_⟩
      show d • w ∈ W
      rw [← algebraMap_smul K d w]
      exact W.smul_mem _ hw
    have hw' : w = (algebraMap (𝓞 K) K d)⁻¹ • (d • w) := by
      rw [← algebraMap_smul K d w, smul_smul, inv_mul_cancel₀ hd', one_smul]
    rw [hw']
    exact Submodule.smul_mem _ _ (Submodule.subset_span hmem)

theorem span_le_span_sc {a : K} (ha : a ≠ 0) (A : Submodule (𝓞 K) Z) :
    Submodule.span K (A : Set Z) ≤ Submodule.span K (Formalism.EigenvalueLevelCeiling.sc a A : Set Z) := by
  rw [Submodule.span_le]
  intro y hy
  have hm : a • y ∈ Formalism.EigenvalueLevelCeiling.sc a A := Submodule.mem_map.2 ⟨y, hy, rfl⟩
  have hy' : y = a⁻¹ • (a • y) := by rw [smul_smul, inv_mul_cancel₀ ha, one_smul]
  rw [hy']
  exact Submodule.smul_mem _ _ (Submodule.subset_span hm)

theorem locP_subset_span (v : HeightOneSpectrum (𝓞 K)) (L : Submodule (𝓞 K) Z) :
    (Formalism.HermitianLatticesTheory.localization₂ v.asIdeal L : Set Z) ⊆ Submodule.span K (L : Set Z) := by
  intro x hx
  obtain ⟨s, hs, hsx⟩ := hx
  have hs0 : s ≠ 0 := fun h => hs (h ▸ v.asIdeal.zero_mem)
  have hs' : algebraMap (𝓞 K) K s ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).2 hs0
  have hx' : x = (algebraMap (𝓞 K) K s)⁻¹ • (s • x) := by
    rw [← algebraMap_smul K s x, smul_smul, inv_mul_cancel₀ hs', one_smul]
  rw [hx']
  exact Submodule.smul_mem _ _ (Submodule.subset_span hsx)

variable {P : Type} [Group P]

theorem mem_eig_iff (ρ : Representation K P Z) (U : Subgroup P) (ψ : P → 𝓞 K) (x : Z) :
    x ∈ Formalism.EigenvalueLevelCeiling.eig ρ U ψ ↔ ∀ u : U, ρ u x = ((ψ u : 𝓞 K) : K) • x := by
  unfold Formalism.EigenvalueLevelCeiling.eig
  simp only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
    sub_eq_zero]

theorem map_eig (ρ : Representation K P Z) (U : Subgroup P) (ψ : P → 𝓞 K) (e : Z →ₗ[K] Z) (V₀ : Submodule K Z)
    (hp : e ∘ₗ e = e ∧ LinearMap.range e = V₀) (hc : ∀ g : P, e ∘ₗ ρ g = ρ g ∘ₗ e) :
    (Formalism.EigenvalueLevelCeiling.eig ρ U ψ).map e = Formalism.EigenvalueLevelCeiling.eig ρ U ψ ⊓ V₀ := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    refine Submodule.mem_inf.2 ⟨(mem_eig_iff ρ U ψ _).2 fun u => ?_, by rw [← hp.2]; exact LinearMap.mem_range_self e x⟩
    have h := congrArg (fun f : Z →ₗ[K] Z => f x) (hc u)
    simp only [LinearMap.comp_apply] at h
    rw [← h, (mem_eig_iff ρ U ψ x).1 hx u, map_smul]
  · intro x hx
    obtain ⟨hx, hv⟩ := Submodule.mem_inf.1 hx
    rw [← hp.2] at hv
    obtain ⟨y, rfl⟩ := hv
    exact ⟨e y, hx, congrArg (fun f : Z →ₗ[K] Z => f y) hp.1⟩

theorem isLatIn_map (ρ : Representation K P Z) (U : Subgroup P) (ψ : P → 𝓞 K) (e : Z →ₗ[K] Z) (V₀ : Submodule K Z)
    (hp : e ∘ₗ e = e ∧ LinearMap.range e = V₀) (hc : ∀ g : P, e ∘ₗ ρ g = ρ g ∘ₗ e) {A : Submodule (𝓞 K) Z}
    (hfg : A.FG) (hle : A ≤ (Formalism.EigenvalueLevelCeiling.eig ρ U ψ).restrictScalars (𝓞 K))
    (hge : (Formalism.EigenvalueLevelCeiling.eig ρ U ψ : Set Z) ⊆ Submodule.span K (A : Set Z)) :
    Formalism.EigenvalueLevelCeiling.IsLatIn (Formalism.EigenvalueLevelCeiling.eig ρ U ψ ⊓ V₀) (A.map (e.restrictScalars (𝓞 K))) := by
  refine ⟨hfg.map _, ?_⟩
  have hs : Submodule.span K (A : Set Z) = Formalism.EigenvalueLevelCeiling.eig ρ U ψ :=
    le_antisymm (Submodule.span_le.2 fun x hx => hle hx) hge
  rw [Submodule.map_coe, LinearMap.coe_restrictScalars, Submodule.span_image, hs, map_eig ρ U ψ e V₀ hp hc]

end Gen

theorem rankAtPlaces_alg : ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (Bs : DefBase K) (Df : DefSide Bs) (S : IndefData Df) (P : Type) [Group P] [Finite P] (c : OnConst) (O : OnObj S P c), LeafSpan O → LeafData O → LeafProj O → (∀ j (g : P), O.e j ∘ₗ O.ρ j g = O.ρ j g ∘ₗ O.e j) → (AtPair S fun v => ∀ j, (O.ThJ v j).FG ∧ O.ThJ v j ≤ (Formalism.EigenvalueLevelCeiling.eig (O.ρ j) O.U O.ψ).restrictScalars (𝓞 K) ∧ Formalism.HermitianLatticesTheory.localization₂ v.asIdeal (O.Th0 v j) ≤ Formalism.HermitianLatticesTheory.localization₂ v.asIdeal (O.ThJ v j)) → RankAtPlaces O := by
  intro K _ _ _ Bs Df S P _ _ c O hSp hD hPr hc hJ w hw
  have one : ∀ v : HeightOneSpectrum (𝓞 K),
      (∀ j, Formalism.EigenvalueLevelCeiling.IsLatIn ⊤ (O.Th v j) ∧ Formalism.EigenvalueLevelCeiling.IsLatIn ⊤ (O.ThK v j)) →
      (∀ j, (O.Th0 v j).FG ∧ O.Th0 v j ≤ (Formalism.EigenvalueLevelCeiling.eig (O.ρ j) O.U O.ψ).restrictScalars (𝓞 K) ∧
        Formalism.EigenvalueLevelCeiling.sc ((Nat.card O.U : ℕ) : K) (Formalism.EigenvalueLevelCeiling.cut (Formalism.EigenvalueLevelCeiling.eig (O.ρ j) O.U O.ψ) (O.ThK v j)) ≤ O.Th0 v j) →
      (∀ j, (O.ThJ v j).FG ∧ O.ThJ v j ≤ (Formalism.EigenvalueLevelCeiling.eig (O.ρ j) O.U O.ψ).restrictScalars (𝓞 K) ∧
        Formalism.HermitianLatticesTheory.localization₂ v.asIdeal (O.Th0 v j) ≤ Formalism.HermitianLatticesTheory.localization₂ v.asIdeal (O.ThJ v j)) →
      ∀ j, Formalism.EigenvalueLevelCeiling.IsLatIn (O.Zg j) ((O.Th0 v j).map ((O.e j).restrictScalars (𝓞 K))) ∧
        Formalism.EigenvalueLevelCeiling.IsLatIn (O.Zg j) (O.eJ v j) ∧ Formalism.HermitianLatticesTheory.localization₂ v.asIdeal (O.Th0 v j) ≤ Formalism.HermitianLatticesTheory.localization₂ v.asIdeal (O.ThJ v j) := by
    intro v hs hd hj j
    have hU : ((Nat.card O.U : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
    have h0 : (Formalism.EigenvalueLevelCeiling.eig (O.ρ j) O.U O.ψ : Set (Fin (O.nZ j) → K)) ⊆ (Submodule.span K (O.Th0 v j : Set (Fin (O.nZ j) → K)) : Set (Fin (O.nZ j) → K)) := by
      intro x hx
      have h1 : x ∈ Submodule.span K (Formalism.EigenvalueLevelCeiling.cut (Formalism.EigenvalueLevelCeiling.eig (O.ρ j) O.U O.ψ) (O.ThK v j) : Set (Fin (O.nZ j) → K)) := by
        rw [span_cut (hs j).2.2]; exact hx
      exact Submodule.span_mono (fun y hy => (hd j).2.2 hy) (span_le_span_sc hU _ h1)
    have hJs : (Formalism.EigenvalueLevelCeiling.eig (O.ρ j) O.U O.ψ : Set (Fin (O.nZ j) → K)) ⊆ (Submodule.span K (O.ThJ v j : Set (Fin (O.nZ j) → K)) : Set (Fin (O.nZ j) → K)) := by
      intro x hx
      exact Submodule.span_le.2 (fun y hy => locP_subset_span v _ ((hj j).2.2 (Formalism.HermitianLatticesTheory.locBasic_le_locS _ _ hy))) (h0 hx)
    exact ⟨isLatIn_map (O.ρ j) O.U O.ψ (O.e j) (O.V₀ j) (hPr j) (hc j) (hd j).1 (hd j).2.1 h0,
      isLatIn_map (O.ρ j) O.U O.ψ (O.e j) (O.V₀ j) (hPr j) (hc j) (hj j).1 (hj j).2.1 hJs, (hj j).2.2⟩
  exact ⟨one w (hSp w hw).1 (hD w hw).1 (hJ w hw).1, one _ (hSp w hw).2 (hD w hw).2 (hJ w hw).2⟩

end GlobalTheory.OnRankAlg

end
end

section

open NumberField AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.GeoLevel GlobalTheory.LevelCusp GlobalTheory.FrameUnif
open GlobalTheory.Dict (castFr)
open GlobalTheory.FrameNorm (IsUnitFr)
open scoped Matrix

namespace GlobalTheory.GeoLevel

open NumberField AlgebraicGeometry CategoryTheory in
open scoped Matrix in
private lemma mat_lact_castFr_eq_map_mul {E : Type} [Field E] {r : ℕ} {Ψ Ψ' : Finset (E →+* ℂ)}
    (hΨ : Ψ = Ψ') (a : GL (Fin r) E) (x : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame Ψ r) (τ : E →+* ℂ) (hτ : τ ∈ Ψ')
    (hτ₀ : τ ∈ Ψ) :
    _root_.ReciprocityTheory.ChartRestriction.G.FD.mat (_root_.ReciprocityTheory.ChartRestriction.G.FD.lact a (_root_.GlobalTheory.Dict.castFr hΨ x)) ⟨τ, hτ⟩ =
      (a : Matrix (Fin r) (Fin r) E).map τ * _root_.ReciprocityTheory.ChartRestriction.G.FD.mat x ⟨τ, hτ₀⟩ := by
  rfl

open NumberField AlgebraicGeometry CategoryTheory in
open scoped Matrix in
private lemma emb_mulVec_eq_map_mulVec_emb {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
    (τ : E →+* ℂ) (A : Matrix (Fin r) (Fin r) E) (v : Fin r → E) :
    _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ (A *ᵥ v) = (A.map τ) *ᵥ _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ v := by
  funext k

  simp [_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb, Matrix.mulVec, dotProduct, map_sum, map_mul]

open NumberField AlgebraicGeometry CategoryTheory in
open scoped Matrix in
private lemma col_mul_eq_mulVec_col' {r : ℕ} (A M : Matrix (Fin r) (Fin r) ℂ) (j : Fin r) :
    _root_.ReciprocityTheory.ChartRestriction.G.FD.col (A * M) j = A *ᵥ _root_.ReciprocityTheory.ChartRestriction.G.FD.col M j := by
  funext k
  simp [_root_.ReciprocityTheory.ChartRestriction.G.FD.col, Matrix.mulVec, dotProduct, Matrix.mul_apply]


open NumberField AlgebraicGeometry CategoryTheory in
open scoped Matrix in
theorem _root_.GlobalTheory.GeoLevel.perFr_lact_of_isMatch : ∀ (E : Type) [Field E] [NumberField E]
    [IsCMField E] (r : ℕ) (X X' : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) (a : GL (Fin r) E)
    (h : _root_.GlobalTheory.LevelCusp.IsMatch X X' a) (x : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r) (v : Fin r → E)
    (τ : E →+* ℂ) (i : ℕ),
    _root_.Formalism.L2.PjFree.perFr X' (_root_.ReciprocityTheory.ChartRestriction.G.FD.lact a (_root_.GlobalTheory.Dict.castFr h.psi x))
        ((a : Matrix (Fin r) (Fin r) E) *ᵥ v) τ i = _root_.Formalism.L2.PjFree.perFr X x v τ i := by
  intro E _ _ _ r X X' a h x v τ i
  have hΨ := h.psi
  have hp := h.p0
  have hA : IsUnit ((a : Matrix (Fin r) (Fin r) E).map τ).det := by
    have h₀ := (Matrix.isUnits_det_units a).map τ
    rwa [RingHom.map_det] at h₀
  unfold _root_.Formalism.L2.PjFree.perFr
  by_cases hτ : τ ∈ X.Ψ
  · have hτ' : τ ∈ X'.Ψ := hΨ ▸ hτ
    rw [dite_eq_left hτ', dite_eq_left hτ]
    by_cases hi : X.p0 + i < r
    · have hi' : X'.p0 + i < r := hp ▸ hi
      rw [dite_eq_left hi', dite_eq_left hi]
      have hfin : (⟨X'.p0 + i, hi'⟩ : Fin r) = ⟨X.p0 + i, hi⟩ := Fin.ext (by simp [hp])
      rw [hfin, mat_lact_castFr_eq_map_mul hΨ a x τ hτ' hτ, emb_mulVec_eq_map_mulVec_emb, Matrix.mul_inv_rev,
        Matrix.mulVec_mulVec, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hA, Matrix.mul_one]
    · have hi' : ¬ X'.p0 + i < r := hp ▸ hi
      rw [dite_eq_right hi', dite_eq_right hi]
  · have hτ' : τ ∉ X'.Ψ := hΨ ▸ hτ
    rw [dite_eq_right hτ', dite_eq_right hτ]
    by_cases hσ : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.conjEmb τ ∈ X.Ψ
    · have hσ' : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.conjEmb τ ∈ X'.Ψ := hΨ ▸ hσ
      rw [dite_eq_left hσ', dite_eq_left hσ]
      by_cases hj : X.p0 - 1 - i < r
      · have hj' : X'.p0 - 1 - i < r := hp ▸ hj
        rw [dite_eq_left hj', dite_eq_left hj]
        have hfin : (⟨X'.p0 - 1 - i, hj'⟩ : Fin r) = ⟨X.p0 - 1 - i, hj⟩ := Fin.ext (by simp [hp])
        rw [hfin, mat_lact_castFr_eq_map_mul hΨ a x _ hσ' hσ, col_mul_eq_mulVec_col', emb_mulVec_eq_map_mulVec_emb]
        exact h.hermC_eq _ _ _
      · have hj' : ¬ X'.p0 - 1 - i < r := hp ▸ hj
        rw [dite_eq_right hj', dite_eq_right hj]
    · have hσ' : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.conjEmb τ ∉ X'.Ψ := hΨ ▸ hσ
      rw [dite_eq_right hσ', dite_eq_right hσ]

end GlobalTheory.GeoLevel
end

section

set_option autoImplicit false

open Set Matrix MeasureTheory
open GlobalTheory.HermFrame
open scoped ComplexOrder

namespace GlobalTheory.CxForm.LocStokes

theorem integral_del_fn_mul_eq_zero : ∀ {M : Type} [TopologicalSpace M] [CompactSpace M] [T2Space M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] {n : ℕ} (A : GlobalTheory.CxForm.HolAtlas M n) (γ : A.Fld) (χ : M → ℝ) (i : A.ι), A.IsForm γ → A.SmoothOn univ (fun y => (χ y : ℂ)) → tsupport χ ⊆ (A.e i).source → A.integral (A.del (A.fn χ * γ)) = 0 := by
  intro M _ _ _ _ _ _ n A γ χ i hγ hχ hs
  exact integral_del_fn_mul_eq_zero_of_isForm A γ χ i hγ hχ hs
    (GlobalTheory.T.holAtlas_isForm_del A _ (FormMul.isForm_mul A _ _ (A.isForm_fn hχ) hγ))

end GlobalTheory.CxForm.LocStokes
end
