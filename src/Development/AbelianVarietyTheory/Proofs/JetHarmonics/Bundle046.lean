module

public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle004
public import Mathlib.CategoryTheory.MorphismProperty.Descent
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.QSurjective
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsAffineHomOfFlatQuotientOfAffineKernel
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.LocallyOfFinitePresentationDiagMap
public import Formalism.HermitianCurvature.BesselNonvanishingReduction
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ChainRuleSmooth.ExpIntertwine
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.Bundle004
public import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsQuotEquiv
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle002
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle012
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent
public import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Limits.Shapes.Connected
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.AlWellDefSt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Mathlib.Topology.UniformSpace.Matrix
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsRosatiGen
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBLocalB
public import Mathlib.NumberTheory.NumberField.CMField
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion

@[expose] public section

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

namespace ExtensionTorsion

open KernelNoTorsion

variable {S : Scheme.{0}} {T G B : Over S} [GrpObj T] [GrpObj G] [GrpObj B]

noncomputable def torsionHom (q : G ⟶ B) [IsMonHom q] (N : ℕ) : torsion G N ⟶ torsion B N :=
  torsionLift (torsion.ι G N ≫ q) (by rw [← MonObj.pow_comp, torsionι_pow, MonObj.one_comp])

theorem torsionHom_ι (q : G ⟶ B) [IsMonHom q] (N : ℕ) :
    torsionHom q N ≫ torsion.ι B N = torsion.ι G N ≫ q :=
  torsionLift_ι _ _

theorem exists_isPullback_mulN [IsCommMonObj G] (i : T ⟶ G) (q : G ⟶ B) [IsMonHom i] [IsMonHom q]
    (hk : IsPullback i (toUnit _) q (η : 𝟙_ _ ⟶ B)) (N : ℕ)
    {P Q : Over S} {a : P ⟶ G} {b : P ⟶ torsion B N} (hP : IsPullback a b q (torsion.ι B N))
    {s : Q ⟶ P} {r : Q ⟶ torsion G N} (hQ : IsPullback s r b (torsionHom q N)) :
    ∃ (c : P ⟶ T) (t : Q ⟶ T), IsPullback s t c (mulN T N) := by
  have inj : ∀ {W : Over S} {x y : W ⟶ T}, x ≫ i = y ≫ i → x = y := fun h =>
    hk.hom_ext h (toUnit_unique _ _)
  have ex : ∀ {W : Over S} (x : W ⟶ G), x ≫ q = 1 → ∃ y : W ⟶ T, y ≫ i = x := fun x h =>
    ⟨hk.lift x (toUnit _) (by rw [h, Hom.one_def]), hk.lift_fst _ _ _⟩
  have hiq : i ≫ q = 1 := by rw [hk.w, Hom.one_def]
  have hpow : ∀ {W : Over S} (x : W ⟶ torsion G N), (x ≫ torsion.ι G N) ^ N = 1 := fun x => by
    rw [← MonObj.comp_pow, torsionι_pow, MonObj.comp_one]
  obtain ⟨c, hc⟩ := ex (a ^ N) (by
    rw [MonObj.pow_comp, hP.w, ← MonObj.comp_pow, torsionι_pow, MonObj.comp_one])
  have hsr : s ≫ a ≫ q = r ≫ torsion.ι G N ≫ q := by
    rw [hP.w, ← Category.assoc, hQ.w, Category.assoc, torsionHom_ι]
  obtain ⟨t, ht⟩ := ex ((s ≫ a) / (r ≫ torsion.ι G N)) (by
    rw [GrpObj.div_comp, Category.assoc, Category.assoc, hsr, div_self'])
  refine ⟨c, t, ⟨?_⟩, ⟨PullbackCone.isLimitAux' _ fun W => ?_⟩⟩
  · apply inj
    rw [comp_mulN, MonObj.pow_comp, ht, div_pow, hpow, div_one, Category.assoc, hc,
      MonObj.comp_pow]
  · have hW : W.fst ≫ c = W.snd ^ N := by rw [W.condition, comp_mulN]
    have hg : ((W.fst ≫ a) / (W.snd ≫ i)) ^ N = 1 := by
      rw [div_pow, ← MonObj.pow_comp _ _ i, ← hW, Category.assoc, hc, MonObj.comp_pow, div_self']
    have hl : W.fst ≫ b = torsionLift _ hg ≫ torsionHom q N := by
      apply torsion_hom_ext
      rw [Category.assoc, Category.assoc, torsionHom_ι, ← Category.assoc (torsionLift _ hg),
        torsionLift_ι, GrpObj.div_comp, Category.assoc, Category.assoc, hiq, MonObj.comp_one,
        div_one, hP.w]
    refine ⟨hQ.lift W.fst _ hl, hQ.lift_fst _ _ _, ?_, ?_⟩
    · apply inj
      change (_ ≫ t) ≫ i = _
      rw [Category.assoc, ht, GrpObj.comp_div, ← Category.assoc, ← Category.assoc, hQ.lift_fst,
        hQ.lift_snd, torsionLift_ι, div_div_cancel]
    · intro (m : W.pt ⟶ Q) (h1 : m ≫ s = W.fst) (h2 : m ≫ t = W.snd)
      change m = _
      refine hQ.hom_ext (by rw [hQ.lift_fst, h1]) ?_
      apply torsion_hom_ext
      rw [hQ.lift_snd, torsionLift_ι, ← h1, ← h2, Category.assoc, Category.assoc, Category.assoc,
        ht, GrpObj.comp_div, div_div_cancel]

theorem torsionHom_of_mulN (Pr : MorphismProperty Scheme.{0}) [Pr.IsStableUnderBaseChange]
    [Pr.DescendsAlong (@Surjective ⊓ @Flat ⊓ @QuasiCompact)]
    [IsCommMonObj G] (i : T ⟶ G) (q : G ⟶ B) [IsMonHom i] [IsMonHom q]
    [Surjective q.left] [Flat q.left] [QuasiCompact q.left]
    (hk : IsPullback i (toUnit _) q (η : 𝟙_ _ ⟶ B)) (N : ℕ) (h : Pr (mulN T N).left) :
    Pr (torsionHom q N).left := by
  have hP := IsPullback.of_hasPullback q (torsion.ι B N)
  have hQ := IsPullback.of_hasPullback (pullback.snd q (torsion.ι B N)) (torsionHom q N)
  obtain ⟨c, t, H⟩ := exists_isPullback_mulN i q hk N hP hQ
  have hP' := hP.map (Over.forget S)
  refine MorphismProperty.of_isPullback_of_descendsAlong (P := Pr)
    (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) (hQ.map (Over.forget S)) ⟨⟨?_, ?_⟩, ?_⟩ ?_
  · exact MorphismProperty.of_isPullback (P := @Surjective) hP' ‹_›
  · exact MorphismProperty.of_isPullback (P := @Flat) hP' ‹_›
  · exact MorphismProperty.of_isPullback (P := @QuasiCompact) hP' ‹_›
  · exact MorphismProperty.of_isPullback (P := Pr) (H.map (Over.forget S)).flip h

end ExtensionTorsion


open ExtensionTorsion in
theorem isFinite_flat_torsion_of_isGt :
    ∀ (S : Scheme.{0}) (E : SplitExt S) (G : Over S) [GrpObj G] [IsCommMonObj G], E.IsGt G → ∀ N : ℕ, 1 ≤ N → IsFinite (torsion E.B N).hom → Flat (torsion E.B N).hom → IsFinite (torsion G N).hom ∧ Flat (torsion G N).hom := by
  rintro S E G _ _ ⟨D⟩ N hN h1 h2
  have := D.q_hom
  have := D.i_hom
  have := D.q_flat
  have := D.q_surjective
  have := D.q_affine
  have := E.free
  have := E.finite
  have hN' : N ≠ 0 := by omega
  have hf : IsFinite (mulN (splitTorus S E.X) N).left := Diag.isFinite_mulN S E.X hN'
  have hl : Flat (mulN (splitTorus S E.X) N).left := Diag.flat_mulN S E.X hN'
  have := flat_descendsAlong_fpqc
  have := isAffineHom_descendsAlong_fpqc.{0}
  have a1 : Flat (torsionHom D.q N).left :=
    torsionHom_of_mulN @Flat D.i D.q D.isKernel N hl
  have a2 : IsAffineHom (torsionHom D.q N).left :=
    torsionHom_of_mulN @IsAffineHom D.i D.q D.isKernel N inferInstance
  have a3 : UniversallyClosed (torsionHom D.q N).left :=
    torsionHom_of_mulN @UniversallyClosed D.i D.q D.isKernel N inferInstance
  have a4 : LocallyOfFiniteType (torsionHom D.q N).left :=
    torsionHom_of_mulN @LocallyOfFiniteType D.i D.q D.isKernel N inferInstance
  have a5 : IsFinite (torsionHom D.q N).left :=
    (IsFinite.iff_isIntegralHom_and_locallyOfFiniteType _).mpr
      ⟨IsIntegralHom.iff_universallyClosed_and_isAffineHom.mpr ⟨a3, a2⟩, a4⟩
  rw [← Over.w (torsionHom D.q N)]
  exact ⟨inferInstance, inferInstance⟩

end GlobalTheory
end

section

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory

theorem thresholds_of_gapOK : ∀ (k r : ℕ) (h : ℝ), GapOK k r h →
    JF.TransportedAlt k r (aOf r h - 1) 0 ∧ B.AB k r ≤ aOf r h - 1 ∧ AG k r < (aOf r h - 1) / 2 ∧ 0 < aOf r h - 1 := by
  intro k r h hg
  obtain ⟨hk, -, -, h4⟩ := hg
  have hAG : 0 ≤ AG k r := by unfold AG; positivity
  have hA : 9 * ((r : ℝ) + 1) * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 + 3 * AG k r + 2 ≤ aOf r h - 1 := by linarith
  have hN : 0 ≤ 9 * ((r : ℝ) + 1) * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 := by positivity
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold JF.TransportedAlt
    rw [Nat.cast_zero, mul_zero, sub_zero, lt_div_iff₀ (by positivity)]
    nlinarith
  · have hAB : B.AB k r = AG k r / 2 + 1 := by unfold B.AB AG; ring
    rw [hAB]
    linarith
  · linarith
  · linarith

end GlobalTheory
end

section

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal Nat

noncomputable section

namespace GlobalTheory.UnipotentExp


set_option backward.isDefEq.respectTransparency false in
theorem exp_apply_of_pattern {n : ℕ} (P : Fin n → Fin n → Prop)
    (htr : ∀ i m j, P i m → P m j → P i j) (Y : Matrix (Fin n) (Fin n) ℂ)
    (hY : ∀ i j, ¬ P i j → Y i j = 0) (i j : Fin n) (hij : ¬ P i j) :
    NormedSpace.exp Y i j = if i = j then 1 else 0 := by
  have hp : ∀ m : ℕ, ∀ i j, ¬ P i j → (Y ^ (m + 1)) i j = 0 := by
    intro m
    induction m with
    | zero => simpa using hY
    | succ m ih =>
      intro i j h
      rw [pow_succ, Matrix.mul_apply]
      refine Finset.sum_eq_zero fun l _ => ?_
      by_cases h1 : P i l
      · rw [hY l j (fun h2 => h (htr _ _ _ h1 h2)), mul_zero]
      · rw [ih i l h1, zero_mul]
  have h1 : HasSum (fun m : ℕ => ((m ! : ℂ)⁻¹ • Y ^ m)) (NormedSpace.exp Y) := by
    open scoped Matrix.Norms.Operator in
    exact NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) Y
  have h2 : HasSum (fun m : ℕ => ((m ! : ℂ)⁻¹ • Y ^ m) i j) (NormedSpace.exp Y i j) :=
    Pi.hasSum.1 (Pi.hasSum.1 h1 i) j
  have h3 : HasSum (fun m : ℕ => ((m ! : ℂ)⁻¹ • Y ^ m) i j) (((0 ! : ℂ)⁻¹ • Y ^ 0) i j) := by
    refine hasSum_single (f := fun m : ℕ => ((m ! : ℂ)⁻¹ • Y ^ m) i j) 0 ?_
    intro m hm
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm
    rw [Matrix.smul_apply, hp m i j hij, smul_zero]
  rw [h2.unique h3]
  simp [Matrix.one_apply]

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem hasDerivAt_exp_apply {k r : ℕ} (X : Mx k r) (i j : Fin (2 * r + k + 1)) :
    HasDerivAt (fun t : ℝ => NormedSpace.exp ((t : ℂ) • X) i j) (X i j) 0 := by
  have hγ := Formalism.REAL.hasDerivAt_mul_exp_smul_zero (1 : Mx k r) X
  simp only [Matrix.one_mul] at hγ
  exact hasDerivAt_pi.1 (hasDerivAt_pi.1 hγ i) j

theorem hasDerivAt_ell {k r : ℕ} (z : Fin (2 * r + k + 1) → ℂ) (X : Mx k r) :
    HasDerivAt (fun t : ℝ => Formalism.QuantumDeterminants.ell k r z (NormedSpace.exp ((t : ℂ) • X)))
      (Formalism.QuantumDeterminants.ell k r z X) 0 := by
  unfold Formalism.QuantumDeterminants.ell
  refine HasDerivAt.fun_sum fun a _ => ?_
  by_cases h : a.val + 1 < r
  · simp only [dif_pos h]
    exact hasDerivAt_exp_apply X _ _
  · simp only [dif_neg h, Matrix.mulVec, dotProduct]
    exact HasDerivAt.fun_sum fun j _ => (hasDerivAt_exp_apply X _ _).mul_const _

theorem ell_one {k r : ℕ} {z : Fin (2 * r + k + 1) → ℂ} (hz : Formalism.QuantumDeterminants.inWb k r z) :
    Formalism.QuantumDeterminants.ell k r z 1 = 0 := by
  unfold Formalism.QuantumDeterminants.ell
  refine Finset.sum_eq_zero fun a _ => ?_
  split_ifs with h
  · refine Matrix.one_apply_ne ?_
    intro e
    have := congrArg Fin.val e
    simp [Formalism.QuantumDeterminants.eI] at this
  · rw [Matrix.one_mulVec]
    exact hz _ (Or.inl a.isLt)

theorem exp_mem_and_deriv : ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (X : Mx k r), Formalism.QuantumDeterminants.inWb k r z → PI.UpqRep.InLieHpk k r X → (∀ i j : Fin (2 * r + k + 1), ¬ (i < j ∧ ¬ (r ≤ i.val ∧ j.val ≤ r + k)) → X i j = 0) → (∀ t : ℝ, NormedSpace.exp ((t : ℂ) • X) ∈ Formalism.QuantumDeterminants.Nset k r) ∧ HasDerivAt (fun t : ℝ => Formalism.QuantumDeterminants.psi k r z Formalism.QuantumDeterminants.cStd (NormedSpace.exp ((t : ℂ) • X))) (Formalism.QuantumDeterminants.ell k r z X - star (Formalism.QuantumDeterminants.ell k r z X)) 0 := by
  intro k r z X hz hX hP
  refine ⟨fun t => ?_, ?_⟩
  · have key := exp_apply_of_pattern
      (fun i j : Fin (2 * r + k + 1) => i < j ∧ ¬ (r ≤ i.val ∧ j.val ≤ r + k))
      (fun i m j h1 h2 => by
        simp only [Fin.lt_def] at h1 h2 ⊢
        omega)
      ((t : ℂ) • X) (fun i j h => by rw [Matrix.smul_apply, hP i j h, smul_zero])
    refine ⟨CCRuleCW.exp_mem_UH _ _ (CCRuleCW.lie_smul _ X hX t), fun a i h => key _ _ ?_,
      fun i j h1 h2 h3 => key _ _ ?_⟩
    · simp only [Fin.lt_def, Formalism.QuantumDeterminants.eI]
      omega
    · tauto
  · have h1 := (hasDerivAt_ell z X).const_mul Formalism.QuantumDeterminants.cStd
    have h2 : HasDerivAt (fun t : ℝ => (Formalism.QuantumDeterminants.cStd *
        Formalism.QuantumDeterminants.ell k r z (NormedSpace.exp ((t : ℂ) • X))).re)
        (Formalism.QuantumDeterminants.cStd * Formalism.QuantumDeterminants.ell k r z X).re 0 :=
      Complex.reCLM.hasFDerivAt.comp_hasDerivAt (0 : ℝ) h1
    have h3 := (h2.ofReal_comp.const_mul Complex.I).cexp
    unfold Formalism.QuantumDeterminants.psi
    convert h3 using 1
    simp only [Complex.ofReal_zero, zero_smul, NormedSpace.exp_zero, ell_one hz, mul_zero,
      Complex.zero_re, Complex.exp_zero, one_mul]
    apply Complex.ext <;> simp [Formalism.QuantumDeterminants.cStd]
    ring

end GlobalTheory.UnipotentExp
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DatumCoverAdjoint

open GlobalTheory.DatumInverseCharacter

theorem span_image_sup_eq_top {R M J : Type} [CommRing R] [AddCommGroup M] [Module R M] (K : Ideal R)
    (φ : M →ₗ[R] M) (hφ : ∀ a, ∃ b, φ b - a ∈ (K • ⊤ : Submodule R M)) (x : J → M) (s : Set J)
    (h : Submodule.span R (x '' s) ⊔ (K • ⊤ : Submodule R M) = ⊤) :
    Submodule.span R ((fun i => φ (x i)) '' s) ⊔ (K • ⊤ : Submodule R M) = ⊤ := by
  rw [eq_top_iff]
  intro a _
  obtain ⟨b, hb⟩ := hφ a
  have h1 : φ b ∈ Submodule.map φ (Submodule.span R (x '' s) ⊔ (K • ⊤ : Submodule R M)) :=
    Submodule.mem_map_of_mem (by rw [h]; exact Submodule.mem_top)
  rw [Submodule.map_sup, Submodule.map_span, Set.image_image, Submodule.map_smul''] at h1
  have h2 : φ b ∈ Submodule.span R ((fun i => φ (x i)) '' s) ⊔ (K • ⊤ : Submodule R M) :=
    SetLike.le_def.1 (sup_le_sup le_rfl (Submodule.smul_mono le_rfl le_top)) h1
  have := sub_mem h2 (Submodule.mem_sup_right hb)
  rwa [sub_sub_cancel] at this

theorem datum_adjoint : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (n : ℕ) (d : DeltaDat Xo c n), d.l₂.M = l.M * d.pd → d.l₂.Mb = l.Mb * d.I → ∀ (ph : (Fin n → LaJ Xo c d) → c.F) (ψ : (LaI Xo c d ≃ₗ[𝓞 E] LaI Xo c d) →* c.Fˣ) (x₀ : Fin n → LaJ Xo c d), d.PhiPin ph ψ x₀ → ∀ g : Sim Dw, (∀ a, g.f d.l₂.M a - a ∈ d.I • (⊤ : Submodule (𝓞 E) Dw.La)) → ∃ σq : LevQ Dw d.l₂ ≃ LevQ Dw d.l₂, (∀ a, σq (Submodule.Quotient.mk a) = Submodule.Quotient.mk (g.f d.l₂.M a)) ∧ ∀ (rk : Bool) (x0 : Fin n → Dw.La), AdmX (l := l) rk x0 → ∃ x0' : Fin n → Dw.La, AdmX (l := l) rk x0' ∧ ∀ q : Fin n → LevQ Dw d.l₂, d.w x0 (fun b => σq.symm (q b)) = d.w x0' q := by
  intro E _ _ _ H Dw l Xo c n d hM hb ph ψ x₀ hpin g hg
  obtain ⟨-, -, -, -, -, hφ⟩ := hpin
  have hM₂ : 0 < d.l₂.M := by have := d.l₂.three_le; omega
  have hM₁ : 0 < l.M := by have := l.three_le; omega
  have hpd : 0 < d.pd := Nat.pos_of_mul_pos_left (hM ▸ hM₂)
  have hIJ := half_prod hM hb
  have hspan : ∀ (l' : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H),
      ((l'.M : ℕ) : 𝓞 E) ∈ l'.Mb * l'.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) := fun l' => by
    rw [l'.prod]; exact Ideal.mem_span_singleton_self _
  have hbI : d.l₂.Mb ≤ d.I := hb ▸ (Ideal.mul_le_inf.trans inf_le_right)
  have hbM : d.l₂.Mb ≤ l.Mb := hb ▸ (Ideal.mul_le_inf.trans inf_le_left)
  have hmb : ((d.l₂.M : ℕ) : 𝓞 E) ∈ d.l₂.Mb := (Ideal.mul_le_inf.trans inf_le_left) (hspan d.l₂)
  have hmJ : ((d.l₂.M : ℕ) : 𝓞 E) ∈ Mfr l :=
    Ideal.map_mono hbM ((Ideal.mul_le_inf.trans inf_le_right) (hspan d.l₂))
  obtain ⟨g', hg'⟩ := g.inv d.l₂.M hM₂
  set f := g.f d.l₂.M with hf
  obtain ⟨σ, hσ⟩ := exists_quot_equiv Dw hmb f g' hg'
  obtain ⟨fa, hfa⟩ := exists_adjoint Dw f
  obtain ⟨ga, hga⟩ := exists_adjoint Dw g'
  have hsurj : ∀ a, ∃ b, ga b - a ∈ (Mfr l • ⊤ : Submodule (𝓞 E) Dw.La) := fun a =>
    ⟨fa a, mem_of_modN Dw hmJ (modN_of_dvd Dw hM₂ fun v => by
      rw [map_sub, LinearMap.sub_apply, hga, hfa, ← map_sub]
      exact dvd_of_modN Dw a (hg' v).2)⟩
  refine ⟨σ.toEquiv, hσ, fun rk x0 hx => ⟨fun b => ga (x0 b),
    span_image_sup_eq_top (Mfr l) ga hsurj x0 _ hx, fun q => ?_⟩⟩
  have hq : ∀ b, f (levRep (σ.toEquiv.symm (q b))) - levRep (q b) ∈ (d.l₂.Mb • ⊤ : Submodule (𝓞 E) Dw.La) := by
    intro b
    rw [← Submodule.Quotient.eq, ← hσ, levRep_spec, levRep_spec]
    exact σ.apply_symm_apply _
  have hz : zetaM c ^ pairL (l := l) x0 (fun b => levRep (σ.toEquiv.symm (q b))) =
      zetaM c ^ pairL (l := l) (fun b => ga (x0 b)) (fun b => levRep (q b)) := by
    refine zpow_congr hM₁ (root_pow c dvd_rfl) ?_
    unfold pairL
    rw [← Finset.sum_sub_distrib]
    refine Finset.dvd_sum fun b _ => ?_
    rw [hga, g'.map_smul, ← map_sub, ← smul_sub]
    refine dvd_right Dw l.prod (cSep_mem l) _ ?_
    set a := levRep (σ.toEquiv.symm (q b))
    have h1 : g' (f a - levRep (q b)) ∈ (l.Mb • ⊤ : Submodule (𝓞 E) Dw.La) := by
      have := Submodule.mem_map_of_mem (f := g') (hq b)
      rw [Submodule.map_smul''] at this
      exact Submodule.smul_mono hbM le_top this
    have h2 : g' (f a) - a ∈ (l.Mb • ⊤ : Submodule (𝓞 E) Dw.La) :=
      mem_of_modN Dw (hbM hmb) (hg' a).1
    have := sub_mem h1 h2
    convert this using 1
    rw [map_sub]
    abel
  have hroot := root_pow d.c₂ (N := d.pd) (hM ▸ Dvd.intro_left _ rfl)
  have hδ : d.eF (d.φδ (fun b => σ.toEquiv.symm (q b))) = d.eF (d.φδ q) := by
    rw [hφ, hφ]
    refine finsum_congr fun x => ?_
    congr 1
    refine zpow_congr hpd hroot ?_
    rw [← Finset.sum_sub_distrib]
    refine Finset.dvd_sum fun b _ => ?_
    rw [← map_sub, ← smul_sub]
    refine dvd_right Dw hIJ (cHalf_mem d.I) _ ?_
    have := sub_mem (Submodule.smul_mono hbI le_rfl (hq b)) (hg (levRep (σ.toEquiv.symm (q b))))
    convert this using 1
    abel
  unfold DeltaDat.w
  rw [hz, map_mul, map_mul, hδ]

end GlobalTheory.DatumCoverAdjoint
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj IsLocalRing NumberField

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TorsionFactsCompare

open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor

section Operators

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]

end Operators

section Data

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
  (D : DegData V (maximalIdeal V)) (F : Type) [Field F] [Algebra (FractionRing V) F]


open QForm in
theorem bOf_balance {ϖ : V} (hϖ : Irreducible ϖ) {Q : D.toPre.X → ℤ} {O : Type} [Ring O] [StarRing O]
    [Module O D.toPre.X] (ιD : D.toPre.OAct O) (hQ : IsQ D.toPre ϖ Q) (a : O) (χ χ' : D.toPre.X) :
    bOf D.toPre Q (a • χ) χ' = bOf D.toPre Q χ (star a • χ') := by
  have hL := D.toPre.P.isLB
  have := ιD.onB.hom a
  have := ιD.onB.hom (star a)
  obtain ⟨u, hu, hnorm⟩ := exists_ros GlobalTheory.globalFns_holds D.toPre.P.isAb D.toPre.P.isLB _ _ (ιD.onB.rosati a)
  have hc := ιD.tau_bal a u hu hnorm χ χ'
  obtain ⟨_, _, hsA, hA⟩ := tau_val hϖ D hQ (a • χ) χ'
  obtain ⟨_, _, hsB, hB⟩ := tau_val hϖ D hQ χ (star a • χ')
  have hu0 := genHasVal_pullGen_of (ϖ := ϖ) D.toPre.P.L _ _ u hu (lift (D.toPre.c χ) (D.toPre.c χ')).left
    (D.toPre.pt2 χ χ') (by simp [DegPre.pt2, ← CartesianMonoidalCategory.comp_lift])
  have h1 := genHasVal_mulGen hϖ D.toPre.P.L hL _ _ _ _ _ _ _ _ _ _ hA hu0
  have := genHasVal_unique hϖ D.toPre.P.L hL _ _ _ _ _
    (genHasVal_corr hϖ D.toPre.P.L hL D.toPre.P.A.hom _ _ _ _ _ _ _ _
      (sumElim_sec hsA (fun k => by
        obtain ⟨q, hq⟩ := rosatiφ_over D.toPre.P.A (ιD.onB.act a) (ιD.onB.act (star a)) k
        show (_ ≫ rosatiφ D.toPre.P.A (ιD.onB.act a) (ιD.onB.act (star a)) k) ≫ _ = _
        rw [hq]; exact over_sec _ _)) hsB _ _
      (genHasVal_isGen D.toPre.P.L _ _ _ _ _ hB) hc h1) hB
  linarith

end Data

section Unif

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
  {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {t : SAB H (Sp V)}
  (P : PELUnif (maximalIdeal V) t) (F : Type) [Field F] [Algebra (FractionRing V) F]

end Unif

end GlobalTheory.TorsionFactsCompare
end
end
