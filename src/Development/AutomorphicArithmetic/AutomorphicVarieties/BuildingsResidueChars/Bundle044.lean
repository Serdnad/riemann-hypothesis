module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsNormalisedThetaSub
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
public import Mathlib.RingTheory.AdicCompletion.Noetherian
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DenseRangeUnits
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InertialOrderFifteenCharAuxiliaryPrimeSpec
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle092
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PartsConj
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
import Mathlib.Algebra.Module.StablyFree.Basic
public import Development.AbelianVarietyTheory.Counterexamples.NonGaloisSurvey.Bundle002
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.RingTheory.Coalgebra.CoassocSimps
import Mathlib.RingTheory.PiTensorProduct
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
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasExponentZeroIff
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.ContinuousTorusCharacter
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.ContinuousResP
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.RepAlg
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

@[expose] public section

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi
open UpperTheory.V.W (Plc)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem conjSrc_eq {E : Type} [Field E] [NumberField E] (τ : E ≃+* E) (w : HeightOneSpectrum (𝓞 E)) :
    conjSrc τ w = preplace τ w :=
  HeightOneSpectrum.ext ((GlobalTheory.Mem.Chr.conjPl_iff_comap _ _ _).1 (conjPl_conjSrc _ w))

private theorem normV_preplace {K : Type} [Field K] [NumberField K] (τ : K ≃+* K) (v : HeightOneSpectrum (𝓞 K)) :
    normV (preplace τ v) = normV v := by
  show Nat.card (𝓞 K ⧸ (preplace τ v).asIdeal) = Nat.card (𝓞 K ⧸ v.asIdeal)
  refine Nat.card_congr (Ideal.quotientEquiv _ _ (RingOfIntegers.mapRingEquiv τ) ?_).toEquiv
  exact (Ideal.map_comap_of_surjective (RingOfIntegers.mapRingEquiv τ : 𝓞 K →+* 𝓞 K)
    (RingOfIntegers.mapRingEquiv τ).surjective v.asIdeal).symm

private theorem isFrob_conjGal {K Ω : Type} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] {τ : K ≃+* K} {σ : Ω ≃+* Ω}
    (h : IsLift τ σ) {A A' : ValuationSubring Ω} (hA : ∀ x, σ x ∈ A' ↔ x ∈ A) {q : ℕ} {g : _root_.Formalism.ConjugateSelfDual.G K Ω}
    (hg : IsFrob (F := K) A' q g) : IsFrob (F := K) A q (conjGal h g) := by
  refine ⟨conjGal_mem_Dec h hA hg.1, fun x hx => ?_⟩
  rw [← val_lt_one hA, map_sub, apply_conjGal, map_pow]
  exact hg.2 _ ((A'.valuation_le_one_iff _).2 ((hA x).2 ((A.valuation_le_one_iff _).1 hx)))

private theorem isLift_conj {F Ω : Type} [Field F] [NumberField F] [IsCMField F] [Field Ω] [Algebra F Ω]
    {c : _root_.Formalism.ConjugateSelfDual.G (maximalRealSubfield F) Ω} (hc : Af.IsConjEl c) :
    IsLift (IsCMField.complexConj F).toRingEquiv c.symm.toRingEquiv := by
  obtain ⟨j, hj⟩ := hc
  intro x
  refine c.symm_apply_eq.2 (j.injective ?_)
  rw [hj]
  have h := IsCMField.complexEmbedding_complexConj F (j.comp (algebraMap F Ω)) x
  exact (Complex.conj_conj _).symm.trans (congrArg (starRingEnd ℂ) h.symm)

theorem UpperTheory.thetaChar_eq_self_of_conjugate_dual :
    ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (art : Ideles E →* Gab E Ω), IsGlobalArtin art → ∀ (κ : HChar E) (m : ℕ), 0 < m → κ.OrderDvd m → ∀ β : _root_.Formalism.ConjugateSelfDual.G E Ω →* (Qbar l)ˣ, Continuous β → IsLAdicOf art ι κ 0 β → ∀ c : _root_.Formalism.ConjugateSelfDual.G (maximalRealSubfield E) Ω, Af.IsConjEl c → (∀ s s' : _root_.Formalism.ConjugateSelfDual.G E Ω, s'.restrictScalars (maximalRealSubfield E) = c * s.restrictScalars (maximalRealSubfield E) * c⁻¹ → β s' = (β s)⁻¹) → GlobalTheory.ThetaPull.thetaChar κ = κ := by
  intro E Ω _ _ _ _ _ _ l _ ι art ha κ m _ _ β _ hL c hc hβ
  have hLi := isLift_conj hc
  have hval : ∀ v, κ.UnrAt v → κ.UnrAt (conjSrc (IsCMField.complexConj E).toRingEquiv v) →
      κ.val (conjSrc (IsCMField.complexConj E).toRingEquiv v) = (κ.val v)⁻¹ := by
    intro v hv hv'
    rw [conjSrc_eq] at hv' ⊢
    obtain ⟨A, hA⟩ := exists_isPlaceOver Ω v
    obtain ⟨σ, hσ⟩ := ReciprocityTheory.Gal.exists_isFrob hA
    have hAA : ∀ y, c.symm.toRingEquiv y ∈ A ↔ y ∈ A.comap c.symm.toRingEquiv.toRingHom := fun _ => Iff.rfl
    have e1 := hL.frob_unr ha (Or.inr rfl) hv hA hσ
    have e2 := hL.frob_unr ha (Or.inr rfl) hv' (isPlaceOver_preplace hLi hAA hA) (σ := conjGal hLi σ)
      (by rw [normV_preplace]; exact isFrob_conjGal hLi hAA hσ)
    rw [hβ σ (conjGal hLi σ) (AlgEquiv.ext fun _ => rfl), Units.val_inv_eq_inv_val, e1, inv_inj, ← map_inv₀] at e2
    exact Units.ext (by rw [Units.val_inv_eq_inv_val]; exact (ι.symm.injective e2).symm)
  have hu := GlobalTheory.GalChar.unr_ae κ
  have hu' := (Function.LeftInverse.injective (GlobalTheory.ThetaPull.conjSrc_conjSrc (E := E))).tendsto_cofinite.eventually hu
  have hS := Filter.eventually_cofinite.1 (hu.and hu')
  have h : (GlobalTheory.ThetaPull.thetaChar κ).1 * κ.1⁻¹ = 1 := by
    refine GlobalTheory.FrobDense.eq_one_of_away _ ((GlobalTheory.ThetaPull.thetaChar κ).2.1.mul κ.2.1.inv) (fun k => ?_) hS.toFinset
      fun v hv => ?_
    · rw [MonoidHom.mul_apply, MonoidHom.inv_apply, κ.2.2, (GlobalTheory.ThetaPull.thetaChar κ).2.2, inv_one, one_mul]
    · rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq, not_not] at hv
      obtain ⟨v, rfl⟩ : ∃ v', conjSrc (IsCMField.complexConj E).toRingEquiv v' = v := ⟨_, GlobalTheory.ThetaPull.conjSrc_conjSrc v⟩
      rw [GlobalTheory.ThetaPull.conjSrc_conjSrc] at hv
      refine GlobalTheory.FrobDense.eq_one_of_unif (((GlobalTheory.ThetaPull.thetaChar κ).1 * κ.1⁻¹).comp (localIdele E _)) fun y hy => ?_
      have hy' : IsUnifAt v (Units.map (conjLoc _ v).toMonoidHom y) := ((conjLoc_spec _ v).2.2 y.val).trans hy
      have h1 : κ.1 (localIdele E _ y) = κ.val _ := κ.val_eq hv.1 y hy
      have h2 : κ.1 (localIdele E v _) = κ.val v := κ.val_eq hv.2 _ hy'
      rw [MonoidHom.comp_apply, MonoidHom.mul_apply, MonoidHom.inv_apply, GlobalTheory.ThetaPull.thetaChar_apply,
        GlobalTheory.ThetaPull.conjAd_localIdele, h1, h2, hval v hv.2 hv.1, mul_inv_cancel]
  exact Subtype.ext (mul_inv_eq_one.1 h)
end

section

open Module Topology

private theorem span_padicInt_fg_of_bounded {l : ℕ} [Fact (Nat.Prime l)] {n : ℕ} (S : Set (Fin n → ℚ_[l])) (C : ℝ)
    (hS : ∀ v ∈ S, ‖v‖ ≤ C) : (Submodule.span ℤ_[l] S).FG := by
  have hl : (1 : ℝ) < l := by exact_mod_cast (Fact.out : Nat.Prime l).one_lt
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt C hl
  let φ : (Fin n → ℤ_[l]) →ₗ[ℤ_[l]] (Fin n → ℚ_[l]) :=
    { toFun := fun c i => ((l : ℚ_[l]) ^ (-(k : ℤ))) * (c i : ℚ_[l])
      map_add' := by
        intro a b
        ext i
        simp [mul_add]
      map_smul' := by
        intro r a
        ext i
        simp [Algebra.smul_def]
        ring }
  refine Submodule.FG.of_le (Submodule.fg_range φ) ?_
  rw [Submodule.span_le]
  intro v hv
  have hbound : ∀ i, ‖(l : ℚ_[l]) ^ (k : ℤ) * v i‖ ≤ 1 := by
    intro i
    rw [norm_mul, Padic.norm_p_zpow]
    have h1 : ‖v i‖ ≤ (l : ℝ) ^ k := (norm_le_pi_norm v i).trans ((hS v hv).trans hk.le)
    calc (l : ℝ) ^ (-(k : ℤ)) * ‖v i‖ ≤ (l : ℝ) ^ (-(k : ℤ)) * (l : ℝ) ^ k := by gcongr
      _ = 1 := by
        rw [zpow_neg, ← zpow_natCast, inv_mul_cancel₀]
        exact (zpow_pos (by linarith) _).ne'
  refine ⟨fun i => ⟨(l : ℚ_[l]) ^ (k : ℤ) * v i, hbound i⟩, ?_⟩
  ext i
  show ((l : ℚ_[l]) ^ (-(k : ℤ))) * ((l : ℚ_[l]) ^ (k : ℤ) * v i) = v i
  have hne : (l : ℚ_[l]) ≠ 0 := by exact_mod_cast (Fact.out : Nat.Prime l).ne_zero
  rw [← mul_assoc, ← zpow_add₀ hne]
  simp

private theorem extendOfIsLattice_repr_eq_repr {l : ℕ} [Fact (Nat.Prime l)] {n m : ℕ}
    (L : Submodule ℤ_[l] (Fin n → ℚ_[l])) [Submodule.IsFullLattice ℚ_[l] L]
    (b : Module.Basis (Fin m) ℤ_[l] L) (y : L) (i : Fin m) :
    (b.extendOfIsFullLattice ℚ_[l]).repr (y : Fin n → ℚ_[l]) i = (b.repr y i : ℚ_[l]) := by
  conv_lhs => rw [← b.sum_repr y]

  rw [Submodule.coe_sum, map_sum, Finset.sum_apply']
  simp_rw [Submodule.coe_smul_of_tower]
  have h : ∀ j, (b.repr y j • (b j : Fin n → ℚ_[l])) = ((b.repr y j : ℚ_[l]) • b.extendOfIsFullLattice ℚ_[l] j) := by
    intro j
    rw [Module.Basis.extendOfIsFullLattice_apply, algebra_compatible_smul ℚ_[l]]
    rfl
  simp_rw [h, map_smul, Module.Basis.repr_self, Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul]
  simp

theorem UpperTheory.galois_representation_integral_lattice :
    UpperTheory.V.Af.Wd.IntBasis := by
  intro l _ Γ _ _ _ V _ _ _ _ _ ρ hρ
  set n := Module.finrank ℚ_[l] V
  let e0 : Module.Basis (Fin n) ℚ_[l] V := Module.finBasis ℚ_[l] V
  let E : V ≃ₗ[ℚ_[l]] (Fin n → ℚ_[l]) := e0.equivFun
  let A : Γ → (Fin n → ℚ_[l]) →ₗ[ℚ_[l]] (Fin n → ℚ_[l]) := fun g =>
    E.toLinearMap ∘ₗ ρ g ∘ₗ E.symm.toLinearMap
  have hA1 : ∀ x, A 1 x = x := by
    intro x
    simp [A]
  have hAmul : ∀ g h x, A (g * h) x = A g (A h x) := by
    intro g h x
    simp [A, map_mul]
  have hEc : Continuous E := IsModuleTopology.continuous_of_linearMap E.toLinearMap
  let f : Γ → Fin n → (Fin n → ℚ_[l]) := fun g j => A g (Pi.single j 1)
  have hf : Continuous f := by
    refine continuous_pi fun j => ?_
    have : (fun g => f g j) = fun g => E (ρ g (E.symm (Pi.single j 1))) := rfl
    rw [this]
    exact hEc.comp (hρ _)
  obtain ⟨C, hC⟩ := (isCompact_range hf).isBounded.exists_norm_le
  let S : Set (Fin n → ℚ_[l]) := Set.range fun p : Γ × Fin n => A p.1 (Pi.single p.2 1)
  let L : Submodule ℤ_[l] (Fin n → ℚ_[l]) := Submodule.span ℤ_[l] S
  have hfg : L.FG := by
    refine span_padicInt_fg_of_bounded S C ?_
    rintro v ⟨⟨g, j⟩, rfl⟩
    exact (norm_le_pi_norm (f g) j).trans (hC _ ⟨g, rfl⟩)
  have hsingle : ∀ j : Fin n, (Pi.single j 1 : Fin n → ℚ_[l]) ∈ L := by
    intro j
    have : (Pi.single j 1 : Fin n → ℚ_[l]) = A 1 (Pi.single j 1) := (hA1 _).symm
    rw [this]
    exact Submodule.subset_span ⟨(1, j), rfl⟩
  have hspan : Submodule.span ℚ_[l] (L : Set (Fin n → ℚ_[l])) = ⊤ := by
    rw [eq_top_iff, ← (Pi.basisFun ℚ_[l] (Fin n)).span_eq]
    refine Submodule.span_mono ?_
    rintro v ⟨j, rfl⟩
    simpa using hsingle j
  have : Submodule.IsLattice ℚ_[l] L := Submodule.IsLattice.of_fg ℚ_[l] hfg
  have : Submodule.IsFullLattice ℚ_[l] L := ⟨hspan⟩
  have hstab : ∀ g, ∀ x ∈ L, (A g).restrictScalars ℤ_[l] x ∈ L := by
    intro g
    have : L ≤ L.comap ((A g).restrictScalars ℤ_[l]) := by
      rw [Submodule.span_le]
      rintro v ⟨⟨h, j⟩, rfl⟩
      show A g (A h (Pi.single j 1)) ∈ L
      rw [← hAmul]
      exact Submodule.subset_span ⟨(g * h, j), rfl⟩
    exact fun x hx => this hx
  have : Module.Free ℤ_[l] L := Submodule.IsLattice.free ℚ_[l] L
  have : Module.Finite ℤ_[l] L := Submodule.IsLattice.finite ℚ_[l] L
  let b0 := Module.Free.chooseBasis ℤ_[l] L
  let b : Module.Basis (Fin (Fintype.card (Module.Free.ChooseBasisIndex ℤ_[l] L))) ℤ_[l] L :=
    b0.reindex (Fintype.equivFin _)
  let e' := b.extendOfIsFullLattice ℚ_[l]
  let e := e'.map E.symm
  let R : Γ →* Module.End ℤ_[l] L :=
    { toFun := fun g => ((A g).restrictScalars ℤ_[l]).restrict (hstab g)
      map_one' := by
        ext x
        simp [LinearMap.restrict_apply, hA1]
      map_mul' := by
        intro g h
        ext x
        simp [LinearMap.restrict_apply, hAmul] }
  let M : Γ →* Matrix _ _ ℤ_[l] := (LinearMap.toMatrixAlgEquiv b).toMonoidHom.comp R
  have key : ∀ (g : Γ) (i j), ((M g i j : ℤ_[l]) : ℚ_[l]) = (e.repr ((ρ g) (e j))) i := by
    intro g i j
    have h1 : M g i j = b.repr (R g (b j)) i := by
      simp [M, LinearMap.toMatrixAlgEquiv_apply]
    have h2 : e.repr ((ρ g) (e j)) i = e'.repr (A g (b j)) i := by
      simp [e, e', A, Module.Basis.map_repr, Module.Basis.map_apply]
    have h3 : (A g (b j : Fin n → ℚ_[l])) = ((R g (b j) : L) : Fin n → ℚ_[l]) := rfl
    rw [h1, h2, h3, extendOfIsLattice_repr_eq_repr]
  refine ⟨_, e, M, ?_, key⟩
  refine continuous_pi fun i => continuous_pi fun j => ?_
  refine (isometry_subtype_coe.isEmbedding.continuous_iff).2 ?_
  have : (fun g => ((M g i j : ℤ_[l]) : ℚ_[l])) = fun g => e.coord i (ρ g (e j)) := by
    funext g
    rw [key]
    rfl
  show Continuous (fun g => ((M g i j : ℤ_[l]) : ℚ_[l]))
  rw [this]
  exact (IsModuleTopology.continuous_of_linearMap (e.coord i)).comp (hρ _)
end

section

noncomputable section

open Module

namespace UpperTheory

private theorem tri_mul_diag {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) (hA : ∀ i j, j < i → A i j = 0)
    (hB : ∀ i j, j < i → B i j = 0) (i : Fin n) : (A * B) i i = A i i * B i i := by
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_single i (fun k _ hk => ?_) (fun h => absurd (Finset.mem_univ i) h)
  rcases lt_or_gt_of_ne hk with h | h
  · rw [hA i k h, zero_mul]
  · rw [hB k i h, mul_zero]

private theorem tri_avg {G : Type} [Group G] [Finite G] {n : ℕ} (R : G →* Matrix (Fin n) (Fin n) ℂ)
    (hR : ∀ g i j, j < i → R g i j = 0) :
    ∃ P : Matrix (Fin n) (Fin n) ℂ, IsUnit P.det ∧ ∀ g, R g * P = P * Matrix.diagonal (fun i => R g i i) := by
  classical
  letI := Fintype.ofFinite G
  have hm : ∀ g h i, R (g * h) i i = R g i i * R h i i := fun g h i => by
    rw [map_mul]; exact tri_mul_diag _ _ (hR g) (hR h) i
  refine ⟨∑ h, R h * Matrix.diagonal (fun i => R h⁻¹ i i), ?_, fun g => ?_⟩
  · rw [Matrix.det_of_upperTriangular]
    · rw [isUnit_iff_ne_zero, Finset.prod_ne_zero_iff]
      intro i _
      have : (∑ h, R h * Matrix.diagonal (fun i => R h⁻¹ i i)) i i = (Fintype.card G : ℂ) := by
        rw [Matrix.sum_apply]
        have : ∀ h : G, (R h * Matrix.diagonal (fun i => R h⁻¹ i i)) i i = 1 := fun h => by
          rw [Matrix.mul_diagonal, ← hm, mul_inv_cancel, map_one, Matrix.one_apply_eq]
        simp [this]
      rw [this]
      exact_mod_cast Fintype.card_ne_zero
    · intro i j hij
      rw [Matrix.sum_apply]
      refine Finset.sum_eq_zero fun h _ => ?_
      rw [Matrix.mul_diagonal, hR h i j hij, zero_mul]
  · rw [Finset.mul_sum, Finset.sum_mul]
    refine Fintype.sum_equiv (Equiv.mulLeft g) _ _ fun h => ?_
    rw [Equiv.coe_mulLeft, Matrix.mul_assoc, Matrix.diagonal_mul_diagonal, map_mul, Matrix.mul_assoc]
    congr 3
    funext i
    rw [← hm]
    congr 2
    group

theorem tridiagonal_weil_deligne : UpperTheory.V.Af.Wd.TriDiag := by
  intro W I _ _ _ n ρ d hfin ⟨b, hb⟩
  let G := ρ.toHomUnits.range
  haveI : Finite G := by
    haveI : Finite (Set.range ρ) := hfin
    refine Finite.of_injective (fun g : G => (⟨(g.1 : End ℂ W), ?_⟩ : Set.range ρ)) ?_
    · obtain ⟨s, hs⟩ := g.2
      exact ⟨s, by rw [← hs]; rfl⟩
    · intro x y h
      exact Subtype.ext (Units.ext (congrArg Subtype.val h))
  let R : G →* Matrix (Fin n) (Fin n) ℂ :=
    ((LinearMap.toMatrixAlgEquiv b).toMulEquiv.toMonoidHom.comp (Units.coeHom _)).comp G.subtype
  have hRs : ∀ s, R (ρ.toHomUnits.rangeRestrict s) = LinearMap.toMatrix b b (ρ s) := fun s => rfl
  obtain ⟨P, hP, hRP⟩ := tri_avg R (fun g i j hij => by
    obtain ⟨s, rfl⟩ := ρ.toHomUnits.rangeRestrict_surjective g
    rw [hRs]; exact (hb s).1 i j hij)
  let e := Matrix.toLinearEquiv b P hP
  have he : ∀ x, e x = Matrix.toLin b b P x := fun x => rfl
  refine ⟨b.map e, fun s => ?_⟩
  have h1 := hRP (ρ.toHomUnits.rangeRestrict s)
  rw [hRs] at h1
  have h2 : (fun i => LinearMap.toMatrix b b (ρ s) i i) = d s := funext (hb s).2
  rw [h2] at h1
  have h3 : ∀ j, ρ s (b.map e j) = d s j • b.map e j := fun j => by
    have h4 := congrArg (fun M => Matrix.toLin b b M (b j)) h1
    simp only [Matrix.toLin_mul b b b, Matrix.toLin_toMatrix, LinearMap.comp_apply] at h4
    rw [Basis.map_apply, he, h4, ← map_smul]
    congr 1
    rw [Matrix.toLin_self]
    simp [Matrix.diagonal_apply, ite_smul, Finset.sum_ite_eq']
  ext i j
  rw [LinearMap.toMatrix_apply, h3, map_smul, Basis.repr_self, Matrix.diagonal_apply]
  by_cases h : i = j
  · subst h; simp
  · simp [h, Finsupp.single_apply, Ne.symm h]

end UpperTheory
end
end

section

open Module in
theorem UpperTheory.abelianField_window_triple_snoc :
    UpperTheory.V.Af.Wd.TriSnoc := by
  unfold UpperTheory.V.Af.Wd.TriSnoc
  intro k W' W W'' ι _ _ _ _ _ _ _ n T' T T'' f p hf hp hex h1 hT' hT'' d hd hd''
  unfold UpperTheory.V.Af.Wd.IsTri at hd ⊢
  obtain ⟨b', hb'⟩ := hd
  obtain ⟨y, hy0, hyspan⟩ := (finrank_eq_one_iff').1 h1
  obtain ⟨s, hs⟩ := hp y
  have hrange : Submodule.span k (Set.range fun i => f (b' i)) ≤ LinearMap.ker p := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact (hex _).2 ⟨_, rfl⟩
  have hli : LinearIndependent k (Fin.snoc (fun i => f (b' i)) s : Fin (n + 1) → W) := by
    rw [linearIndependent_finSnoc]
    refine ⟨b'.linearIndependent.map' f (LinearMap.ker_eq_bot.2 hf), ?_⟩
    intro hmem
    have h0 : p s = 0 := LinearMap.mem_ker.1 (hrange hmem)
    rw [hs] at h0
    exact hy0 h0
  have hsp : ⊤ ≤ Submodule.span k (Set.range (Fin.snoc (fun i => f (b' i)) s : Fin (n + 1) → W)) := by
    intro w _
    obtain ⟨c, hc⟩ := hyspan (p w)
    have hker : p (w - c • s) = 0 := by rw [map_sub, map_smul, hs, hc, sub_self]
    obtain ⟨x, hx⟩ := (hex _).1 hker
    have hw : w = f x + c • s := by rw [hx]; abel
    rw [hw]
    refine Submodule.add_mem _ ?_ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨Fin.last n, by simp⟩))

    rw [← b'.sum_repr x, map_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [map_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i.castSucc, by simp⟩)
  set b := Module.Basis.mk hli hsp with hbdef
  have hbc : ∀ i, b i.castSucc = f (b' i) := fun i => by simp [b]
  have hbl : b (Fin.last n) = s := by simp [b]
  have hfx : ∀ x : W', f x = ∑ i, (b'.repr x i) • b i.castSucc := by
    intro x
    conv_lhs => rw [← b'.sum_repr x]

    rw [map_sum]
    simp only [map_smul, hbc]
  have hrepr1 : ∀ (x : W') (i : Fin n), b.repr (f x) i.castSucc = b'.repr x i := by
    intro x i
    rw [hfx]

    simp [map_sum, Finsupp.single_apply, Fin.castSucc_inj]
  have hrepr2 : ∀ x : W', b.repr (f x) (Fin.last n) = 0 := by
    intro x
    rw [hfx]

    simp [map_sum]
  refine ⟨b, fun a => ⟨?_, ?_⟩⟩
  · intro i j hji
    rw [LinearMap.toMatrix_apply]
    induction j using Fin.lastCases with
    | last => exact absurd hji (not_lt.2 (Fin.le_last i))
    | cast j =>
      rw [hbc, ← hT']
      induction i using Fin.lastCases with
      | last => exact hrepr2 _
      | cast i =>
        rw [hrepr1]
        have := (hb' a).1 i j (Fin.castSucc_lt_castSucc_iff.1 hji)
        rwa [LinearMap.toMatrix_apply] at this
  · intro i
    rw [LinearMap.toMatrix_apply]
    induction i using Fin.lastCases with
    | last =>
      rw [hbl]
      have hker : p (T a s - d a (Fin.last n) • s) = 0 := by
        rw [map_sub, map_smul, hT'', hs, hd'', sub_self]
      obtain ⟨x, hx⟩ := (hex _).1 hker
      have hTs : T a s = f x + d a (Fin.last n) • s := by rw [hx]; abel
      rw [hTs, map_add (f := _), map_smul, Finsupp.add_apply, Finsupp.smul_apply, hrepr2, ← hbl, b.repr_self]
      simp
    | cast i =>
      rw [hbc, ← hT', hrepr1]
      have := (hb' a).2 i
      rwa [LinearMap.toMatrix_apply] at this
end

section

theorem UpperTheory.galois_rep_values_in_finite_extension :
    UpperTheory.V.Af.Wd.FinVal := by
  intro F Ω C _ _ _ _ M hM χ hχ
  classical
  have hpos : 0 < M := by omega
  have hR : {ζ : Ω | ζ ^ M = 1}.Finite := by
    refine (Multiset.toFinset (Polynomial.nthRoots M (1 : Ω))).finite_toSet.subset ?_
    intro ζ hζ
    simpa [Polynomial.mem_nthRoots hpos] using hζ
  haveI : Finite {ζ : Ω | ζ ^ M = 1} := hR.to_subtype
  let π : (Ω ≃ₐ[F] Ω) → ({ζ : Ω | ζ ^ M = 1} → {ζ : Ω | ζ ^ M = 1}) := fun s ζ =>
    ⟨s ζ, by
      show (s ζ) ^ M = 1
      rw [← map_pow, show (ζ : Ω) ^ M = 1 from ζ.2, map_one]⟩
  have hfac : ∀ s t, π s = π t → χ s = χ t := by
    intro s t hst
    have h1 : χ (t⁻¹ * s) = 1 := by
      refine hχ _ (fun ζ hζ => ?_)
      have h := congrArg (fun f => (f ⟨ζ, hζ⟩ : Ω)) hst
      simp only [π] at h
      rw [AlgEquiv.mul_apply, h, AlgEquiv.aut_inv, AlgEquiv.symm_apply_apply]
    rw [map_mul, map_inv, inv_mul_eq_one] at h1
    exact h1.symm
  refine (Set.finite_range (fun x : Set.range π => χ x.2.choose)).subset ?_
  rintro _ ⟨s, rfl⟩
  exact ⟨⟨π s, s, rfl⟩, hfac _ _ (⟨s, rfl⟩ : π s ∈ Set.range π).choose_spec⟩
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.GalOfCusp

theorem UpperTheory.crystalline_period_ring_properties :
    UpperTheory.V.Af.Wd.BrFacts := by
  classical
  intro F Ω _ _ _ _ _ l _ w A h O _ _ _ Bw hj
  refine ⟨fun c => ?_, fun L s => ?_, fun M hM => ?_⟩
  · have h1 := weilToGK_frobUr hj (frob h) (a := 1) (b := 0) (actsAs_one_iff.2 isFrob_frob) c
    simpa using h1
  · have h2 := GlobalTheory.Survey.CrystallineCharacterRatio.chi_eq_cyc (UpperTheory.V.Loc.PP l) Bw.j _ _ (Bw.e_comm s)
    exact (congrArg (algebraMap ℚ_[l] (Om l)) h2)
  · have hM0 : M ≠ 0 := by omega
    have hfin : ({x : Om l | x ^ M = 1}).Finite := by
      refine (Polynomial.nthRoots M (1 : Om l)).toFinset.finite_toSet.subset fun x hx => ?_
      simpa [Polynomial.mem_nthRoots (Nat.pos_of_ne_zero hM0)] using hx
    haveI := hfin.to_subtype
    have hfd : FiniteDimensional ℚ_[l] (IntermediateField.adjoin ℚ_[l] {x : Om l | x ^ M = 1}) :=
      IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
    refine ⟨⟨_, hfd⟩, fun s hs ζ hζ => Bw.j.injective ?_⟩
    rw [← Bw.e_comm]
    exact (IntermediateField.mem_fixingSubgroup_iff _ _).1 hs _
      (IntermediateField.subset_adjoin _ _ (show Bw.j ζ ^ M = 1 by rw [← map_pow, hζ, map_one]))
end
