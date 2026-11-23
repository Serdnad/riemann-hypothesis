module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle133
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.CoeNonzeroLocusCanonicalEqComplRange
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle091
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.ExistsSecNonzeroLocusEqOfLbIso
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle144
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle100
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle121
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle075
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle098
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle120
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle083
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle143
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.FiltrationCocycleLiftCriterion
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle012
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsNotCongPow
import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle080
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasExponentZeroIff
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle002
import Formalism.ConjugateSelfDual.Bundle001
import ReciprocityTheory.GaloisValuations.GlobalA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DivCalc
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle001
import Formalism.SharpRestriction.InertJacobiLevels.AsmIface

@[expose] public section

section

open NumberField IsDedekindDomain ValuativeRel Matrix MeasureTheory TensorProduct Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory


open GlobalTheory.SmGL in
theorem unipRad_stdBlocks_two_ne_bot : ∀ (R : Type) [CommRing R] [Nontrivial R] (n a b : ℕ) (h : ∑ i, ![a, b] i = n), 0 < a → 0 < b → unipRad R (stdBlocks ![a, b] h) ≠ ⊥ := by
  intro R _ _ n a b h ha hb
  set e := stdBlocks ![a, b] h with he
  let i : Fin n := e ⟨0, ⟨0, by simpa using ha⟩⟩
  let j : Fin n := e ⟨1, ⟨0, by simpa using hb⟩⟩
  have hij : i ≠ j := by
    intro hh
    have := congrArg Sigma.fst (e.injective hh)
    simp at this
  let g : GL (Fin n) R :=
    ⟨Matrix.transvection i j 1, Matrix.transvection i j (-1),
      by
        show Matrix.transvection i j (1 : R) * Matrix.transvection i j (-1) = 1
        rw [Matrix.transvection_mul_transvection_same i j hij]; simp,
      by
        show Matrix.transvection i j (-1 : R) * Matrix.transvection i j 1 = 1
        rw [Matrix.transvection_mul_transvection_same i j hij]; simp⟩
  have hg : (g : Matrix (Fin n) (Fin n) R) = 1 + Matrix.single i j 1 := rfl
  have hmem : g ∈ unipRad R e := by
    rw [mem_unipRad]
    refine ⟨?_, ?_⟩
    · rw [mem_parab]
      intro p q hpq
      have hne : p ≠ q := by rintro rfl; exact lt_irrefl _ hpq
      rw [hg, Matrix.add_apply, Matrix.one_apply_ne hne, zero_add]
      by_cases hp : p = i
      · by_cases hq : q = j
        · subst hp; subst hq
          rw [blk_apply, blk_apply] at hpq
          exact absurd hpq (by decide)
        · rw [Matrix.single_apply, if_neg]
          rintro ⟨_, h'⟩; exact hq h'.symm
      · rw [Matrix.single_apply, if_neg]
        rintro ⟨h', _⟩; exact hp h'.symm
    · intro c x y
      rw [hg, Matrix.add_apply]
      have h1 : (1 : Matrix (Fin n) (Fin n) R) (e ⟨c, x⟩) (e ⟨c, y⟩) = (1 : Matrix _ _ R) x y := by
        by_cases hxy : x = y
        · subst hxy; simp
        · rw [Matrix.one_apply_ne, Matrix.one_apply_ne hxy]
          intro hh
          have := e.injective hh
          simp at this
          exact hxy this
      rw [h1]
      have h2 : Matrix.single i j (1 : R) (e ⟨c, x⟩) (e ⟨c, y⟩) = 0 := by
        rw [Matrix.single_apply]
        split_ifs with hh
        · obtain ⟨h3, h4⟩ := hh
          have e3 := congrArg Sigma.fst (e.injective h3)
          have e4 := congrArg Sigma.fst (e.injective h4)
          simp only at e3 e4
          rw [← e3] at e4
          exact absurd e4 (by decide)
        · rfl
      rw [h2, add_zero]
  intro hbot
  rw [hbot, Subgroup.mem_bot] at hmem
  have := congrArg (fun u : GL (Fin n) R => (u : Matrix (Fin n) (Fin n) R) i j) hmem
  simp [hg, Matrix.one_apply_ne hij] at this

end GlobalTheory
end

section

open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.GaugeEx

theorem twoStep_isProd_of_isStdX (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) (d : ℕ) (b : Module.Basis (Fin d) F E)
    (s : StdMeas b) (M : ℕ) (J : Matrix (Fin (M + 1)) (Fin (M + 1)) E) (x : Fin 1 → Fin (M + 1) → E)
    (a : F) (B : Matrix (Fin (M + 1)) (Fin M) E) (J' : Matrix (Fin M) (Fin M) E)
    (y : Fin 1 → Fin M → E) (c : F) (hS : StepData σ J x a B J') (hc : c ≠ 0)
    (hy : hE σ J' (y 0) (y 0) = algebraMap F E c)
    (ν : Measure (Fin 1 → Fin (M + 1) → AF F ⊗[F] E)) (ν' : Measure (Fin 1 → Fin M → AF F ⊗[F] E))
    (N : Measure (Fin 2 → Fin (M + 1) → AF F ⊗[F] E))
    (hν : IsStdX s σ J a ν) (hν' : IsStdX s σ J' c ν') (hN : TwoStep (AF F) σ J x B ν ν' N) :
    ∃ mi mi' Ni, ∃ (mv : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin 1 → Fin (M + 1) → Fv F v ⊗[F] E))
      (mv' : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin 1 → Fin M → Fv F v ⊗[F] E))
      (Nv : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin 2 → Fin (M + 1) → Fv F v ⊗[F] E)),
      FibAt (Ainf F) σ J (tupMeas s.lamI 1 (M + 1)) s.nuI (algebraMap F _ a) mi ∧
      FibAt (Ainf F) σ J' (tupMeas s.lamI 1 M) s.nuI (algebraMap F _ c) mi' ∧
      TwoStep (Ainf F) σ J x B mi mi' Ni ∧
      (∀ v, FibAt (Fv F v) σ J (tupMeas (s.lamV v) 1 (M + 1)) (s.nuV v) (algebraMap F _ a) (mv v)) ∧
      (∀ v, FibAt (Fv F v) σ J' (tupMeas (s.lamV v) 1 M) (s.nuV v) (algebraMap F _ c) (mv' v)) ∧
      (∀ v, TwoStep (Fv F v) σ J x B (mv v) (mv' v) (Nv v)) ∧ IsProd b N Ni Nv := by
  obtain ⟨mi, mv, hfi, hfv, hP⟩ := hν
  obtain ⟨mi', mv', hfi', hfv', hP'⟩ := hν'
  have hJ : IsHermND σ J := hS.1
  have ha : a ≠ 0 := hS.2.1
  have hx : hE σ J (x 0) (x 0) = algebraMap F E a := hS.2.2.1
  have hJ' : IsHermND σ J' := hS.2.2.2.2.2
  obtain ⟨hNi, hNv⟩ := nice_ainf_fv F
  have oi := GlobalTheory.T.fibreMeasure_invariant_supported_orbit_ne_zero F E σ hCM (Ainf F) hNi (M + 1) J x a s.lamI s.nuI mi hJ ha hx
    s.haar_lamI s.haar_nuI hfi
  have oi' := GlobalTheory.T.fibreMeasure_invariant_supported_orbit_ne_zero F E σ hCM (Ainf F) hNi M J' y c s.lamI s.nuI mi' hJ' hc hy
    s.haar_lamI s.haar_nuI hfi'
  have ov := fun v => GlobalTheory.T.fibreMeasure_invariant_supported_orbit_ne_zero F E σ hCM (Fv F v) (hNv v) (M + 1) J x a (s.lamV v) (s.nuV v)
    (mv v) hJ ha hx (s.haar_lamV v) (s.haar_nuV v) (hfv v)
  have ov' := fun v => GlobalTheory.T.fibreMeasure_invariant_supported_orbit_ne_zero F E σ hCM (Fv F v) (hNv v) M J' y c (s.lamV v) (s.nuV v)
    (mv' v) hJ' hc hy (s.haar_lamV v) (s.haar_nuV v) (hfv' v)
  obtain ⟨Ni, hTi, -⟩ := GlobalTheory.T.existsUnique_unitaryTwoStepPairMeasure F E σ hCM (Ainf F) M J x a B J' mi mi' hS oi.2.1 hP.1.1
    hP'.1.1 oi'.1
  have hTv : ∀ v, ∃ N', TwoStep (Fv F v) σ J x B (mv v) (mv' v) N' := fun v =>
    (GlobalTheory.T.existsUnique_unitaryTwoStepPairMeasure F E σ hCM (Fv F v) M J x a B J' (mv v) (mv' v) hS (ov v).2.1 (hP.1.2.1 v)
      (hP'.1.2.1 v) (ov' v).1).exists
  choose Nv hTv using hTv
  exact ⟨mi, mi', Ni, mv, mv', Nv, hfi, hfi', hTi, hfv, hfv', hTv,
    GlobalTheory.T.adelicTwoStepMeasure_isRestrictedProduct_local F E σ hCM d b M J x a B J' ν mi mv ν' mi' mv' N Ni Nv hS hP hP' oi.2.1
      (fun v => (ov v).2.1) oi'.1 (fun v => (ov' v).1) hTi hTv hN⟩

private theorem prInf_inclR_eq {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
    (e : E) : prInf (inclR (AF F) e) = inclR (Ainf F) e := by
  show (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E)) (1 ⊗ₜ[F] e) = 1 ⊗ₜ[F] e
  first
  | rfl
  | (erw [Algebra.TensorProduct.map_tmul, map_one]; rfl)

private theorem prV_inclR_eq {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
    (v : HeightOneSpectrum (𝓞 F)) (e : E) : prV v (inclR (AF F) e) = inclR (Fv F v) e := by
  show (Algebra.TensorProduct.map (evalV F v) (AlgHom.id F E))
      ((Algebra.TensorProduct.map (sndA F) (AlgHom.id F E)) (1 ⊗ₜ[F] e)) = 1 ⊗ₜ[F] e
  first
  | rfl
  | (erw [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul, map_one, map_one]; rfl)

theorem twoStep_adelic_swap : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (s : StdMeas b), ∀ (M : ℕ) (J : Matrix (Fin (M + 1)) (Fin (M + 1)) E) (x₁ : Fin 1 → Fin (M + 1) → E) (a₁ : F) (B₁ : Matrix (Fin (M + 1)) (Fin M) E) (J₁' : Matrix (Fin M) (Fin M) E) (x₂ : Fin 1 → Fin (M + 1) → E) (a₂ : F) (B₂ : Matrix (Fin (M + 1)) (Fin M) E) (J₂' : Matrix (Fin M) (Fin M) E) (y₁ y₂ : Fin 1 → Fin M → E) (b₁ b₂ : F) (γ : GL (Fin 2) E), StepData σ J x₁ a₁ B₁ J₁' → StepData σ J x₂ a₂ B₂ J₂' → b₁ ≠ 0 → b₂ ≠ 0 → hE σ J₁' (y₁ 0) (y₁ 0) = algebraMap F E b₁ → hE σ J₂' (y₂ 0) (y₂ 0) = algebraMap F E b₂ → ![x₂ 0, B₂.mulVec (y₂ 0)] = lrAct 1 (γ : Matrix (Fin 2) (Fin 2) E) ![x₁ 0, B₁.mulVec (y₁ 0)] → ∀ (ν₁ ν₂ : Measure (Fin 1 → Fin (M + 1) → AF F ⊗[F] E)) (ν₁' ν₂' : Measure (Fin 1 → Fin M → AF F ⊗[F] E)) (N₁ N₂ : Measure (Fin 2 → Fin (M + 1) → AF F ⊗[F] E)), IsStdX s σ J a₁ ν₁ → IsStdX s σ J₁' b₁ ν₁' → IsStdX s σ J a₂ ν₂ → IsStdX s σ J₂' b₂ ν₂' → TwoStep (AF F) σ J x₁ B₁ ν₁ ν₁' N₁ → TwoStep (AF F) σ J x₂ B₂ ν₂ ν₂' N₂ → N₂ = N₁.map (lrAct 1 ((γ : Matrix (Fin 2) (Fin 2) E).map (inclR (AF F)))) := by
  intro F E _ _ _ _ _ σ hCM d b s M J x₁ a₁ B₁ J₁' x₂ a₂ B₂ J₂' y₁ y₂ b₁ b₂ γ hS₁ hS₂ hb₁ hb₂ hy₁
    hy₂ hγ ν₁ ν₂ ν₁' ν₂' N₁ N₂ hν₁ hν₁' hν₂ hν₂' hN₁ hN₂
  obtain ⟨u, hu, hloc⟩ := GlobalTheory.T.twoStepMeasure_orthogonalBasis_swap_local F E σ hCM M J x₁ a₁ B₁ J₁' x₂ a₂ B₂ J₂' y₁ y₂ b₁ b₂ γ
    hS₁ hS₂ hb₁ hb₂ hy₁ hy₂ hγ
  obtain ⟨mi₁, mi₁', Ni₁, mv₁, mv₁', Nv₁, hfi₁, hfi₁', hTi₁, hfv₁, hfv₁', hTv₁, hP₁⟩ :=
    twoStep_isProd_of_isStdX F E σ hCM d b s M J x₁ a₁ B₁ J₁' y₁ b₁ hS₁ hb₁ hy₁ ν₁ ν₁' N₁
      hν₁ hν₁' hN₁
  obtain ⟨mi₂, mi₂', Ni₂, mv₂, mv₂', Nv₂, hfi₂, hfi₂', hTi₂, hfv₂, hfv₂', hTv₂, hP₂⟩ :=
    twoStep_isProd_of_isStdX F E σ hCM d b s M J x₂ a₂ B₂ J₂' y₂ b₂ hS₂ hb₂ hy₂ ν₂ ν₂' N₂
      hν₂ hν₂' hN₂
  obtain ⟨hNi, hNv⟩ := nice_ainf_fv F

  have ei := hloc (Ainf F) hNi s.lamI s.nuI mi₁ mi₂ mi₁' mi₂' Ni₁ Ni₂ s.haar_lamI s.haar_nuI
    hfi₁ hfi₁' hfi₂ hfi₂' hTi₁ hTi₂
  have ev := fun v => hloc (Fv F v) (hNv v) (s.lamV v) (s.nuV v) (mv₁ v) (mv₂ v) (mv₁' v)
    (mv₂' v) (Nv₁ v) (Nv₂ v) (s.haar_lamV v) (s.haar_nuV v) (hfv₁ v) (hfv₁' v) (hfv₂ v)
    (hfv₂' v) (hTv₁ v) (hTv₂ v)

  have hmap := GlobalTheory.T.isRestrictedProductTupleMeasure_map_leftRightAction F E d b 2 (M + 1) N₁ Ni₁ Nv₁ 1
    (Matrix.GeneralLinearGroup.map (inclR (AF F)) γ) hP₁
  have hγA : ((Matrix.GeneralLinearGroup.map (inclR (AF F)) γ : GL (Fin 2) (AF F ⊗[F] E)) :
      Matrix (Fin 2) (Fin 2) (AF F ⊗[F] E)) = (γ : Matrix (Fin 2) (Fin 2) E).map (inclR (AF F)) :=
    rfl
  have hγi : ((γ : Matrix (Fin 2) (Fin 2) E).map (inclR (AF F))).map prInf =
      (γ : Matrix (Fin 2) (Fin 2) E).map (inclR (Ainf F)) := by
    ext i j; exact prInf_inclR_eq _
  have hγv : ∀ v, ((γ : Matrix (Fin 2) (Fin 2) E).map (inclR (AF F))).map (prV v) =
      (γ : Matrix (Fin 2) (Fin 2) E).map (inclR (Fv F v)) := by
    intro v; ext i j; exact prV_inclR_eq v _
  have h1i : (1 : Matrix (Fin (M + 1)) (Fin (M + 1)) (AF F ⊗[F] E)).map prInf = 1 :=
    Matrix.map_one _ (map_zero _) (map_one _)
  have h1v : ∀ v, (1 : Matrix (Fin (M + 1)) (Fin (M + 1)) (AF F ⊗[F] E)).map (prV v) = 1 :=
    fun v => Matrix.map_one _ (map_zero _) (map_one _)
  rw [hγA] at hmap
  simp only [Units.val_one, h1i, h1v, hγi, hγv] at hmap

  obtain ⟨hfin, hprod⟩ := GlobalTheory.T.product_formula_haarModulus_cmField_element F E σ hCM u hu
  have hsc := GlobalTheory.T.restrictedProduct_measure_smul_factors_eq_smul F E d b 2 (M + 1) _ _ _ (modu (Ainf F ⊗[F] E) (inclR (Ainf F) u))
    (fun v => modu (Fv F v ⊗[F] E) (inclR (Fv F v) u)) hmap hfin
  simp only [hprod, one_smul] at hsc
  have hv : Nv₂ = fun v => modu (Fv F v ⊗[F] E) (inclR (Fv F v) u) •
      (Nv₁ v).map (lrAct 1 ((γ : Matrix (Fin 2) (Fin 2) E).map (inclR (Fv F v)))) := funext ev
  rw [← ei, ← hv] at hsc
  exact ((GlobalTheory.T.restrictedProductMeasure_basic_properties F E d b 2 (M + 1) N₂ Ni₂ Nv₂ hP₂).2.2.1 _ hsc).symm

end GlobalTheory.GaugeEx
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
  ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.ProjSpace GlobalTheory.Cartier

namespace GlobalTheory.ProjBlowup

private theorem gm_id_val_eq_germ {X : Scheme.{0}} {V : X.Opens} (y : X) (hy : y ∈ V) (a : Γ(X, V)ˣ) :
    (gm (𝟙 X) y V a).val = X.presheaf.germ V y hy a.val := by
  simp only [gm, pullU, dif_pos (show (𝟙 X) y ∈ V from hy)]
  simp
  rfl

private theorem germ_res_val_eq_germ {X : Scheme.{0}} {V W : X.Opens} (h : W ≤ V) (y : X) (hy : y ∈ W)
    (a : Γ(X, V)ˣ) : X.presheaf.germ W y hy (res h a).val = X.presheaf.germ V y (h hy) a.val := by
  simp [res]

theorem isLB_of_chartPull_id {X : Scheme.{0}} {A B : LB X} (hB : B.IsLB) (a : ChartPull A B (𝟙 X))
    (hc : ⨆ i, A.U i = ⊤) : A.IsLB := {
  cover := hc
  g_self := by
    obtain ⟨idx, hle, hg⟩ := a
    intro i
    apply Units.ext
    refine TopCat.Presheaf.section_ext X.sheaf _ _ _ (fun y hy => ?_)
    have hy' : y ∈ B.U (idx i) := hle i hy
    change X.presheaf.germ (A.U i) y hy (res _ (A.g i i)).val = X.presheaf.germ (A.U i) y hy (1 : Γ(X, A.U i)ˣ).val
    rw [germ_res_val_eq_germ, ← gm_id_val_eq_germ, hg y i i hy hy,
      gm_id_val_eq_germ y (show y ∈ B.U (idx i) ⊓ B.U (idx i) from ⟨hy', hy'⟩),
      ← germ_res_val_eq_germ (le_inf le_rfl le_rfl : B.U (idx i) ≤ _) y hy', hB.g_self (idx i)]
    simp
  cocycle := by
    obtain ⟨idx, hle, hg⟩ := a
    intro i j k
    apply Units.ext
    refine TopCat.Presheaf.section_ext X.sheaf _ _ _ (fun y hy => ?_)
    have hi : y ∈ A.U i := hy.1.1
    have hj : y ∈ A.U j := hy.1.2
    have hk : y ∈ A.U k := hy.2
    have hi' : y ∈ B.U (idx i) := hle i hi
    have hj' : y ∈ B.U (idx j) := hle j hj
    have hk' : y ∈ B.U (idx k) := hle k hk
    change X.presheaf.germ _ y hy ((res _ (A.g i j)).val * (res _ (A.g j k)).val) =
      X.presheaf.germ _ y hy (res _ (A.g i k)).val
    rw [map_mul, germ_res_val_eq_germ, germ_res_val_eq_germ, germ_res_val_eq_germ, ← gm_id_val_eq_germ, ← gm_id_val_eq_germ,
      ← gm_id_val_eq_germ, hg y i j hi hj, hg y j k hj hk, hg y i k hi hk,
      gm_id_val_eq_germ y (show y ∈ B.U (idx i) ⊓ B.U (idx j) from ⟨hi', hj'⟩),
      gm_id_val_eq_germ y (show y ∈ B.U (idx j) ⊓ B.U (idx k) from ⟨hj', hk'⟩),
      gm_id_val_eq_germ y (show y ∈ B.U (idx i) ⊓ B.U (idx k) from ⟨hi', hk'⟩)]
    have hB3 := congrArg (fun u : Γ(X, B.U (idx i) ⊓ B.U (idx j) ⊓ B.U (idx k))ˣ =>
      X.presheaf.germ _ y (show y ∈ B.U (idx i) ⊓ B.U (idx j) ⊓ B.U (idx k) from ⟨⟨hi', hj'⟩, hk'⟩) u.val)
      (hB.cocycle (idx i) (idx j) (idx k))
    simp only [Units.val_mul, map_mul, germ_res_val_eq_germ] at hB3
    exact hB3 }

private theorem gm_id_res_eq {X : Scheme.{0}} {U V : X.Opens} (h : V ≤ U) (y : X) (hy : y ∈ V)
    (a : Γ(X, U)ˣ) : gm (𝟙 X) y V (res h a) = gm (𝟙 X) y U a := by
  apply Units.ext
  rw [gm_id_val_eq_germ y hy, gm_id_val_eq_germ y (h hy), germ_res_val_eq_germ]

private theorem gs_resG_eq {X Y : Scheme.{0}} (f : Y ⟶ X) (y : Y) {U V : X.Opens} (h : V ≤ U) (hy : f y ∈ V)
    (a : Γ(X, U)) : gs f y V (resG X h a) = gs f y U a :=
  gs_res f y h hy a

private theorem mul_eq_unit_mul_of_relations {S : Type _} [CommRing S] (G t t' : Sˣ) (ap aq fp fq sp sq : S)
    (h5 : (t' : S) * t = 1) (E1 : sp = ap * fp) (E2 : sq = aq * fq) (E3 : sp = G * sq) (E4 : fp = t * fq) :
    ap * fp = ((G * t' : Sˣ) : S) * aq * fp := by
  rw [Units.val_mul]
  linear_combination (-1 : S) * E1 + E3 + (G : S) * E2 - ((G : S) * aq * fq) * h5 - ((G : S) * t' * aq) * E4

theorem lbIso_pull_O1_of_proportional (R : Type) [CommRing R] (X W : Scheme.{0}) (J : X.IdealSheafData)
    (L₀ : LB X) (m : ℕ) (σ : Fin (m + 1) → L₀.Sec) (g : W ⟶ X) (ψ : W ⟶ PSpace R m) (D : GlobalTheory.EffCartierData W)
    (hL : L₀.IsLB) (hJ : Generates J σ) (hP : Proportional σ g ψ) (hD : D.idealSheaf = J.comap g) :
    LBIso ((GlobalTheory.ProjSpace.O1 R m).pull ψ) (GlobalTheory.CechPic.tens (L₀.pull g) (GlobalTheory.CechPic.dual D.lb)) := by
  classical
  have hT : (GlobalTheory.CechPic.tens (L₀.pull g) (GlobalTheory.CechPic.dual D.lb)).IsLB :=
    GlobalTheory.CechPic.isLB_tens (pull_isLB hL g) (GlobalTheory.CechPic.isLB_dual D.isLB_lb)
  have hGA := generatesAlong_comap_of_generates X W J L₀ m σ g hJ
  rw [← hD] at hGA
  have loc : ∀ (k : L₀.ι) (d : D.ι) (A : W.affineOpens) (hk : A.1 ≤ g ⁻¹ᵁ L₀.U k) (hd : A.1 ≤ D.U d),
      ∃ a c : Fin (m + 1) → Γ(W, A.1), (∀ j, (g.appLE (L₀.U k) A.1 hk).hom ((σ j).f k) =
        a j * resG W hd (D.f d)) ∧ ∑ j, c j * a j = 1 := by
    intro k d A hk hd
    refine exists_quot_of_span_eq (D.regular d A.1 hd) ?_
    rw [← D.ideal_idealSheaf A d hd, hGA.2 k A hk]
  let Idx := {p : L₀.ι × D.ι × W.affineOpens // p.2.2.1 ≤ g ⁻¹ᵁ L₀.U p.1 ∧ p.2.2.1 ≤ D.U p.2.1}
  let tI : Idx → (GlobalTheory.CechPic.tens (L₀.pull g) (GlobalTheory.CechPic.dual D.lb)).ι := fun p => (fun _ => p.1.1, p.1.2.1)
  have hle : ∀ p : Idx, p.1.2.2.1 ≤ (GlobalTheory.CechPic.tens (L₀.pull g) (GlobalTheory.CechPic.dual D.lb)).U (tI p) :=
    fun p y hy => ⟨mem_pull.2 (p.2.1 hy), p.2.2 hy⟩
  let N : LB W :=
    { ι := Idx
      U := fun p => p.1.2.2.1
      g := fun p q => res (inf_le_inf (hle p) (hle q))
        ((GlobalTheory.CechPic.tens (L₀.pull g) (GlobalTheory.CechPic.dual D.lb)).g (tI p) (tI q)) }
  let cp : ChartPull N (GlobalTheory.CechPic.tens (L₀.pull g) (GlobalTheory.CechPic.dual D.lb)) (𝟙 W) :=
    ⟨tI, hle, fun y p q hp hq => gm_id_res_eq _ y (show y ∈ N.U p ⊓ N.U q from ⟨hp, hq⟩) _⟩
  have hcov : ⨆ p, N.U p = ⊤ := by
    refine eq_top_iff.2 (fun y _ => ?_)
    have hgy : g y ∈ ⨆ k, L₀.U k := by rw [hL.cover]; trivial
    obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 hgy
    obtain ⟨d, hd⟩ := D.exists_mem y
    obtain ⟨A, hyA, hA⟩ := GlobalTheory.EffCartierData.exists_affine_le (X := W)
      (show y ∈ g ⁻¹ᵁ L₀.U k ⊓ D.U d from ⟨hk, hd⟩)
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨(k, d, A), hA.trans inf_le_left, hA.trans inf_le_right⟩, hyA⟩
  have hN : N.IsLB := isLB_of_chartPull_id hT cp hcov
  have H2 : LBIso N (GlobalTheory.CechPic.tens (L₀.pull g) (GlobalTheory.CechPic.dual D.lb)) := GlobalTheory.CechPic.iso_of_chart hT cp
  choose af cf haf hcf using fun p : Idx => loc p.1.1 p.1.2.1 p.1.2.2 p.2.1 p.2.2
  have hcomp : ∀ (j : Fin (m + 1)) (p q : Idx),
      resG W (inf_le_left : N.U p ⊓ N.U q ≤ N.U p) (af p j) =
        (N.g p q : Γ(W, N.U p ⊓ N.U q)) * resG W (inf_le_right : N.U p ⊓ N.U q ≤ N.U q) (af q j) := by
    intro j p q
    have hV : N.U p ⊓ N.U q ≤ D.U p.1.2.1 := inf_le_left.trans p.2.2
    refine (mul_cancel_right_mem_nonZeroDivisors (D.regular p.1.2.1 _ hV)).1 ?_
    refine fn_ext (fun y hy => ?_)
    have hyp : y ∈ p.1.2.2.1 := hy.1
    have hyq : y ∈ q.1.2.2.1 := hy.2
    rw [gs_mul (𝟙 W) y _ hy, gs_mul (𝟙 W) y _ hy, gs_mul (𝟙 W) y _ hy, gs_resG_eq _ y _ hy,
      gs_resG_eq _ y _ hy, gs_resG_eq _ y _ hy, gs_unit (𝟙 W) y _ hy]
    change _ = (gm (𝟙 W) y _ (res _ _)).val * _ * _
    rw [gm_id_res_eq _ y hy, GlobalTheory.CechPic.gm_tens _ _ _ y _ _ (hle p hyp) (hle q hyq),
      gm_pull_g L₀ g (𝟙 W) y _ _ (hle p hyp).1 (hle q hyq).1]
    have E1 := congrArg (gs (𝟙 W) y (N.U p)) (haf p j)
    rw [gs_appLE g _ _ _ (𝟙 W) y hyp, gs_mul _ _ _ hyp, gs_resG_eq _ _ _ hyp] at E1
    have E2 := congrArg (gs (𝟙 W) y (N.U q)) (haf q j)
    rw [gs_appLE g _ _ _ (𝟙 W) y hyq, gs_mul _ _ _ hyq, gs_resG_eq _ _ _ hyq] at E2
    have hk2 : (𝟙 W ≫ g) y ∈ L₀.U p.1.1 ⊓ L₀.U q.1.1 := ⟨p.2.1 hyp, q.2.1 hyq⟩
    have E3 := congrArg (gs (𝟙 W ≫ g) y (L₀.U p.1.1 ⊓ L₀.U q.1.1)) ((σ j).compat p.1.1 q.1.1)
    rw [gs_res _ _ _ hk2, gs_mul _ _ _ hk2, gs_unit _ _ _ hk2, gs_res _ _ _ hk2] at E3
    have hd2 : (𝟙 W) y ∈ D.U p.1.2.1 ⊓ D.U q.1.2.1 := ⟨p.2.2 hyp, q.2.2 hyq⟩
    have E4 := congrArg (gs (𝟙 W) y (D.U p.1.2.1 ⊓ D.U q.1.2.1)) (D.trans_spec p.1.2.1 q.1.2.1)
    rw [gs_resG_eq _ _ _ hd2, gs_mul _ _ _ hd2, gs_unit _ _ _ hd2, gs_resG_eq _ _ _ hd2] at E4
    have E5 : ((gm (𝟙 W) y ((GlobalTheory.CechPic.dual D.lb).U (tI p).2 ⊓ (GlobalTheory.CechPic.dual D.lb).U (tI q).2))
        ((GlobalTheory.CechPic.dual D.lb).g (tI p).2 (tI q).2)).val *
        (gm (𝟙 W) y (D.U p.1.2.1 ⊓ D.U q.1.2.1) (D.trans p.1.2.1 q.1.2.1)).val = 1 := by
      change (gm (𝟙 W) y (D.U p.1.2.1 ⊓ D.U q.1.2.1) (D.trans p.1.2.1 q.1.2.1)⁻¹).val *
        (gm (𝟙 W) y (D.U p.1.2.1 ⊓ D.U q.1.2.1) (D.trans p.1.2.1 q.1.2.1)).val = 1
      rw [← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one]
    exact mul_eq_unit_mul_of_relations _ _ _ _ _ _ _ _ _ E5 E1 E2 E3 E4
  let t : Fin (m + 1) → N.Sec := fun j => { f := fun p => af p j, compat := fun p q => hcomp j p q }
  have ht : ⨆ i, Out.nonzeroLocus (t i) = ⊤ := by
    refine eq_top_iff.2 (fun y _ => ?_)
    have hy : y ∈ ⨆ p, N.U p := by rw [hcov]; trivial
    obtain ⟨p, hyp⟩ := TopologicalSpace.Opens.mem_iSup.1 hy
    obtain ⟨j, hj⟩ := exists_mem_basicOpen_of_sum (hcf p) hyp
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨j, GlobalTheory.basicOpen_le_nonzeroLocus (t j) p hj⟩
  have hch : ∀ y : W, ∃ i, y ∈ ψ ⁻¹ᵁ chart R m i := by
    intro y
    have h := iSup_nonzeroLocus_secPull (iSup_nonzeroLocus_coord R m) ψ
    have hy : y ∈ ⨆ i, Out.nonzeroLocus (secPull (coord R m i) ψ) := by rw [h]; trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hy
    refine ⟨i, ?_⟩
    have e := toProj_preimage_chart (ψ ≫ PSpace.str R m) (fun i => secPull (coord R m i) ψ)
      (iSup_nonzeroLocus_secPull (iSup_nonzeroLocus_coord R m) ψ) i
    rw [toProj_secPull_coord] at e
    rw [e]
    exact hi
  have hψ : ψ = toProj (ψ ≫ PSpace.str R m) t ht := by
    refine eq_toProj_of_locally (s := t) ht rfl (fun y => ?_)
    have hy : y ∈ ⨆ p, N.U p := by rw [hcov]; trivial
    obtain ⟨p, hyp⟩ := TopologicalSpace.Opens.mem_iSup.1 hy
    obtain ⟨i, hi⟩ := hch y
    refine ⟨N.U p ⊓ ψ ⁻¹ᵁ chart R m i, ⟨hyp, hi⟩, p, inf_le_left, i, inf_le_right,
      resG W inf_le_left (af p i), fun j => ?_⟩
    have hV : N.U p ⊓ ψ ⁻¹ᵁ chart R m i ≤ D.U p.1.2.1 := inf_le_left.trans p.2.2
    have hk' : N.U p ⊓ ψ ⁻¹ᵁ chart R m i ≤ g ⁻¹ᵁ L₀.U p.1.1 := inf_le_left.trans p.2.1
    refine (mul_cancel_right_mem_nonZeroDivisors (D.regular p.1.2.1 _ hV)).1 ?_
    refine fn_ext (fun z hz => ?_)
    have hzp : z ∈ N.U p := hz.1
    have Ej := congrArg (gs (𝟙 W) z (N.U p)) (haf p j)
    rw [gs_appLE g _ _ _ (𝟙 W) z hzp, gs_mul _ _ _ hzp, gs_resG_eq _ _ _ hzp] at Ej
    have Ei := congrArg (gs (𝟙 W) z (N.U p)) (haf p i)
    rw [gs_appLE g _ _ _ (𝟙 W) z hzp, gs_mul _ _ _ hzp, gs_resG_eq _ _ _ hzp] at Ei
    have Eh := congrArg (gs (𝟙 W) z _) (hP _ p.1.1 hk' i inf_le_right j)
    rw [gs_appLE g _ _ _ (𝟙 W) z hz, gs_mul _ _ _ hz, gs_appLE g _ _ _ (𝟙 W) z hz] at Eh
    rw [gs_mul _ _ _ hz, gs_mul _ _ _ hz, gs_mul _ _ _ hz, gs_resG_eq _ _ _ hz, gs_resG_eq _ _ _ hz,
      gs_resG_eq _ _ _ hz]
    linear_combination (-1 : W.presheaf.stalk z) * Ej + Eh + gs (𝟙 W) z _ (pullRatio ψ _ i inf_le_right j) * Ei
  have H1 : LBIso ((O1 R m).pull ψ) N := by
    have h := lbIso_pullback_O1_toProj (ψ ≫ PSpace.str R m) t ht
    rw [← hψ] at h
    exact h
  exact LBIso.trans (pull_isLB (O1_isLB R m) ψ) hN hT H1 H2

end GlobalTheory.ProjBlowup
end
end

section

open Finset ArithmeticFunction NumberField IsDedekindDomain Filter Topology GlobalTheory.Mem.An Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab
open scoped nonZeroDivisors

namespace GlobalTheory

theorem kroneckerTwo_neg_eq_jacobiSym_two (q : ℕ) (hq : q % 4 = 3) :
    GlobalTheoryTheory.kron2 (-(q : ℤ)) = jacobiSym 2 q := by
  have hodd : Odd q := Nat.odd_iff.mpr (by omega)
  rw [jacobiSym.at_two hodd, ZMod.χ₈_nat_eq_if_mod_eight]
  unfold GlobalTheoryTheory.kron2
  split_ifs <;> omega

theorem kronSym_neg_eq_jacobiSym_and_two :
    (∀ q n : ℕ, q % 4 = 3 → 0 < n → GlobalTheoryTheory.kronSym (-(q : ℤ)) n = jacobiSym (n : ℤ) q) ∧
      ∀ n : ℕ, Odd n → GlobalTheoryTheory.kronSym 2 n = ZMod.χ₈ (n : ZMod 8) := by
  refine ⟨fun q n hq hn => ?_, fun n hn => ?_⟩
  · unfold GlobalTheoryTheory.kronSym
    have hodd : Odd (n / 2 ^ n.factorization 2) := by
      have h := Nat.not_dvd_ordCompl Nat.prime_two hn.ne'
      exact Nat.odd_iff.mpr (by omega)
    have hmul : 2 ^ n.factorization 2 * (n / 2 ^ n.factorization 2) = n :=
      Nat.ordProj_mul_ordCompl_eq_self n 2
    rw [jacobiSym_neg_eq_of_three_mod_four q _ hq hodd, kroneckerTwo_neg_eq_jacobiSym_two q hq,
      ← jacobiSym.pow_left, ← jacobiSym.mul_left]
    congr 1
    rw [mul_comm]
    exact_mod_cast hmul
  · unfold GlobalTheoryTheory.kronSym
    have h0 : n.factorization 2 = 0 :=
      Nat.factorization_eq_zero_of_not_dvd (by have := Nat.odd_iff.mp hn; omega)
    rw [h0, pow_zero, pow_zero, Nat.div_one, mul_one, jacobiSym.at_two hn]

end GlobalTheory
end
