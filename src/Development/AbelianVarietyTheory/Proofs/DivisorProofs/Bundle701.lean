module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle629
public import Mathlib.Order.CompletePartialOrder
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle668
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle651
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle045
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle667
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankOfMulEqOne
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle008
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilRepresentationOfLatticeVacua
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EmbGLMemRealSU
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieLatticeDualIndex
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.EffectiveEpi.Comp
import Mathlib.CategoryTheory.ExtremalEpi
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Dynamics.Ergodic.Action.Regular
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle017
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle013
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Monoidal.Mon
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.QuadTie
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle007

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
open GlobalTheory.UPel.HT GlobalTheory.UPel.HT.LieType

theorem _root_.GlobalTheory.T.ringOfIntegersJointEigenspace_disjoint_biSup : ∀ (F : Type) [Field F] [NumberField F] (g : ℕ) (φ : 𝓞 F →+* Matrix (Fin g) (Fin g) ℂ) (s : Finset (F →+* ℂ)) (τ : F →+* ℂ), τ ∉ s → Disjoint (eigSp φ τ) (⨆ τ' ∈ s, eigSp φ τ') := by
  first | exact @GlobalTheory.UPel.HT.LieType.eigSp_disjoint_biSup | exact GlobalTheory.UPel.HT.LieType.eigSp_disjoint_biSup | (intros; apply GlobalTheory.UPel.HT.LieType.eigSp_disjoint_biSup <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.SWQ GlobalTheory.ThetaTransform
open scoped Matrix Classical

noncomputable section

namespace GlobalTheory.ThetaTransform

theorem symV_realLine_eq_zero : ∀ (F : Type) [Field F] [NumberField F] (N : ℕ), IsTotallyReal F →
    ∀ M : ℝ →+ VA F N, IsRealLine M → ∀ t s : ℝ, symV (M t) (M s) = 0 := by
  intro F _ _ N hF M hM t s

  let φ : InfinitePlace F → AF F →+* ℝ := fun w =>
    (InfinitePlace.Completion.extensionEmbeddingOfIsReal (hF.isReal w)).comp
      ((Pi.evalRingHom (fun v : InfinitePlace F => v.Completion) w).comp (fstA F).toRingHom)
  have hφ : ∀ w (x : AF F), φ w x = InfinitePlace.Completion.extensionEmbeddingOfIsReal (hF.isReal w)
      (x.1 w) := fun _ _ => rfl
  have hcont : ∀ w (g : ℝ → AF F), Continuous g → Continuous fun r => φ w (g r) := by
    intro w g hg
    simp only [hφ]
    exact (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal (hF.isReal w)).continuous.comp
      ((continuous_apply w).comp (continuous_fst.comp hg))
  have lin : ∀ (p : VA F N →+ AF F), Continuous p → ∀ w r, φ w (p (M r)) = r * φ w (p (M 1)) := by
    intro p hp w r
    let f : ℝ →+ ℝ := ((φ w).toAddMonoidHom.comp p).comp M
    have hc : Continuous f := hcont w (fun r => p (M r)) (hp.comp hM.1)
    have := map_real_smul f hc r 1
    simpa [f] using this
  have p1 : ∀ l : Fin N, Continuous ((LinearMap.proj l : (Fin N → AF F) →ₗ[ℤ] AF F).toAddMonoidHom.comp
      (AddMonoidHom.fst _ _) : VA F N →+ AF F) := fun l =>
    (continuous_apply l).comp continuous_fst
  have p2 : ∀ l : Fin N, Continuous ((LinearMap.proj l : (Fin N → AF F) →ₗ[ℤ] AF F).toAddMonoidHom.comp
      (AddMonoidHom.snd _ _) : VA F N →+ AF F) := fun l =>
    (continuous_apply l).comp continuous_snd
  have k1 : ∀ l w r, φ w ((M r).1 l) = r * φ w ((M 1).1 l) := fun l w r => lin _ (p1 l) w r
  have k2 : ∀ l w r, φ w ((M r).2 l) = r * φ w ((M 1).2 l) := fun l w r => lin _ (p2 l) w r
  have hfst : fstA F (symV (M t) (M s)) = 0 := by
    funext w
    apply (InfinitePlace.Completion.extensionEmbeddingOfIsReal (hF.isReal w)).injective
    have h : φ w (symV (M t) (M s)) = 0 := by

      simp only [symV, dotProduct, map_sub, map_sum, map_mul]
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_eq_zero fun l _ => ?_
      rw [k1 l w t, k1 l w s, k2 l w t, k2 l w s]
      ring
    exact h.trans (map_zero _).symm
  have h0 : ∀ r l, sndA F ((M r).1 l) = 0 ∧ sndA F ((M r).2 l) = 0 := fun r l =>
    ⟨congrFun (hM.2 r).1 l, congrFun (hM.2 r).2 l⟩
  have hsnd : sndA F (symV (M t) (M s)) = 0 := by

    simp only [symV, dotProduct, map_sub, map_sum, map_mul, (h0 _ _).1, (h0 _ _).2, zero_mul,
    Finset.sum_const_zero, sub_zero]
  exact Prod.ext hfst hsnd

end GlobalTheory.ThetaTransform
end
end

section

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.SWQ GlobalTheory.GaugeEx
open scoped Matrix Pointwise

namespace GlobalTheory.ThetaTransform

variable {F : Type} [Field F] [NumberField F] {N : ℕ} [Invertible (2 : AF F)] {ψ : AddChar (AF F) ℂ}

theorem integrand_periodic {f : VA F N → ℂ} (hf : QuasiV ψ f) (x y : Fin N → AF F) (b : Fin N → F) :
    f (x, rat b + y) * ψ (-(⅟(2 : AF F) * (x ⬝ᵥ (rat b + y)))) = f (x, y) * ψ (-(⅟(2 : AF F) * (x ⬝ᵥ y))) := by
  have h0 : (rat (0 : Fin N → F) : Fin N → AF F) = 0 := by funext l; simp [rat]
  have h := hf 0 b (x, y)
  rw [h0, Prod.mk_add_mk, zero_add] at h
  rw [h, mul_right_comm, ← AddChar.map_add_eq_mul, mul_comm]
  congr 2
  simp only [symV, dotProduct_add, zero_dotProduct]
  ring

theorem invV_heisV_fst (ν : Measure (AF F)) (𝓓 : Set (Fin N → AF F)) (f : VA F N → ℂ) (u x : Fin N → AF F) :
    invV ψ ν 𝓓 (heisV ψ (u, 0) f) x = invV ψ ν 𝓓 f (x + u) := by
  unfold invV
  congr 1
  funext y
  rw [heisV, mul_right_comm, ← AddChar.map_add_eq_mul, mul_comm, Prod.mk_add_mk, add_zero]
  congr 2
  simp only [symV, add_dotProduct, dotProduct_zero]
  ring

theorem invV_heisV_snd {ν : Measure (AF F)} (hν : IsCov1 ν) {𝓓 : Set (Fin N → AF F)}
    (hD : IsAddFundamentalDomain (ratSub F N) 𝓓 (muV N ν)) {f : VA F N → ℂ} (hf : QuasiV ψ f) (u x : Fin N → AF F) :
    invV ψ ν 𝓓 (heisV ψ (0, u) f) x = ψ (x ⬝ᵥ u) * invV ψ ν 𝓓 f x := by
  obtain ⟨hH, hmem, -, -, -⟩ := GlobalTheory.SWQ.rat_lattice_fundamentalDomain F N ν hν
  have : Countable F := (Module.finBasis ℚ F).equivFun.injective.countable
  have : Countable (ratSub F N) := by
    refine Set.Countable.to_subtype ((Set.countable_range (rat : (Fin N → F) → (Fin N → AF F))).mono fun v hv => ?_)
    obtain ⟨ξ, h⟩ := (hmem v).1 hv
    exact ⟨ξ, h.symm⟩
  let P : (Fin N → AF F) → ℂ := fun y => f (x, y) * ψ (-(⅟(2 : AF F) * (x ⬝ᵥ y)))
  have hP : ∀ (g : ratSub F N) (y : Fin N → AF F), P (g +ᵥ y) = P y := by
    rintro ⟨g, hg⟩ y
    obtain ⟨ξ, rfl⟩ := (hmem g).1 hg
    exact integrand_periodic hf x y ξ
  have e1 : invV ψ ν 𝓓 (heisV ψ (0, u) f) x = ψ (x ⬝ᵥ u) * ∫ y in 𝓓, P (y + u) ∂(muV N ν) := by
    unfold invV
    rw [← integral_const_mul]
    congr 1
    funext y
    simp only [heisV, P, Prod.mk_add_mk, add_zero]
    rw [mul_right_comm, ← AddChar.map_add_eq_mul, mul_left_comm, ← AddChar.map_add_eq_mul, mul_comm]
    congr 2
    simp only [symV, dotProduct_add, zero_dotProduct]
    linear_combination two_mul_invOf (x ⬝ᵥ u)
  rw [e1]
  congr 1
  have hmp : MeasurePreserving (fun y : Fin N → AF F => y + u) (muV N ν) (muV N ν) := measurePreserving_add_right _ u
  have hemb : MeasurableEmbedding (fun y : Fin N → AF F => y + u) := measurableEmbedding_addRight u
  have hD' : IsAddFundamentalDomain (ratSub F N) (u +ᵥ 𝓓) (muV N ν) := hD.vadd_of_comm u
  have e2 : 𝓓 = (fun y : Fin N → AF F => y + u) ⁻¹' (u +ᵥ 𝓓) := by
    ext y
    rw [Set.mem_preimage, add_comm]
    exact Set.vadd_mem_vadd_set_iff.symm
  conv_lhs => rw [e2]
  rw [hmp.setIntegral_preimage_emb hemb P]
  exact hD'.setIntegral_eq hD hP

end GlobalTheory.ThetaTransform

end
end

section

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.SWQ GlobalTheory.ThetaTransform
open scoped Matrix Classical

namespace GlobalTheory.ThetaTransform

theorem continuous_heisV_snd {F : Type} [Field F] [NumberField F] {N : ℕ} [Invertible (2 : AF F)]
    (ψ : AddChar (AF F) ℂ) (hψ : Continuous ψ) (u : VA F N) (g : VA F N → ℂ) (hg : Continuous g)
    (x : Fin N → AF F) : Continuous fun y : Fin N → AF F => heisV ψ u g (x, y) := by
  unfold heisV symV
  have h1 : Continuous fun y : Fin N → AF F => (x, y).1 ⬝ᵥ u.2 - u.1 ⬝ᵥ (x, y).2 := by
    simp only [dotProduct]
    fun_prop
  refine (hψ.comp (continuous_const.mul h1)).mul (hg.comp ?_)
  fun_prop

theorem heisV_zero {F : Type} [Field F] [NumberField F] {N : ℕ} [Invertible (2 : AF F)]
    (ψ : AddChar (AF F) ℂ) (g : VA F N → ℂ) : heisV ψ 0 g = g := by
  funext w
  simp [heisV, symV, AddChar.map_zero_eq_one]

open GlobalTheory.GaugeEx in
theorem hasDerivAt_invV_heisV : ∀ (F : Type) [Field F] [NumberField F] (N : ℕ) [Invertible (2 : AF F)] (ψ : AddChar (AF F) ℂ) (lam : InfinitePlace F → ℝ) (ν : Measure (AF F)), Ctx ψ lam ν (half F N) → ∀ 𝓓 : Set (Fin N → AF F), IsAddFundamentalDomain (ratSub F N) 𝓓 (muV N ν) → muV N ν 𝓓 = 1 → ∀ (f f' : VA F N → ℂ) (C : ℝ), Continuous f → Continuous f' → (∀ w, ‖f w‖ ≤ C) → (∀ w, ‖f' w‖ ≤ C) → ∀ M : ℝ →+ VA F N, Continuous M → (∀ w s, HasDerivAt (fun t : ℝ => heisV ψ (M t) f w) (heisV ψ (M s) f' w) s) → ∀ x, HasDerivAt (fun t : ℝ => invV ψ ν 𝓓 (heisV ψ (M t) f) x) (invV ψ ν 𝓓 f' x) 0 := by
  intro F _ _ N _ ψ lam ν hC 𝓓 _ h1 f f' C hf hf' hfC hf'C M _ hM x
  have hψ := hC.2.1
  haveI : IsFiniteMeasure ((muV N ν).restrict 𝓓) := isFiniteMeasure_restrict.2 (by rw [h1]; simp)
  have hcont : ∀ (u : VA F N) (g : VA F N → ℂ), Continuous g →
      Continuous fun y : Fin N → AF F => heisV ψ u g (x, y) * ψ (-(⅟(2 : AF F) * (x ⬝ᵥ y))) := by
    intro u g hg
    refine (continuous_heisV_snd ψ hψ.1 u g hg x).mul (hψ.1.comp ?_)
    simp only [dotProduct]
    fun_prop
  have hnorm : ∀ (u : VA F N) (g : VA F N → ℂ), (∀ w, ‖g w‖ ≤ C) → ∀ y : Fin N → AF F,
      ‖heisV ψ u g (x, y) * ψ (-(⅟(2 : AF F) * (x ⬝ᵥ y)))‖ ≤ C := by
    intro u g hg y
    simp only [heisV, norm_mul, hψ.2.1, one_mul, mul_one]
    exact hg _
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := (muV N ν).restrict 𝓓)
    (F := fun t y => heisV ψ (M t) f (x, y) * ψ (-(⅟(2 : AF F) * (x ⬝ᵥ y))))
    (F' := fun t y => heisV ψ (M t) f' (x, y) * ψ (-(⅟(2 : AF F) * (x ⬝ᵥ y))))
    (x₀ := (0 : ℝ)) (bound := fun _ => C) (s := Set.univ) Filter.univ_mem
    (Filter.Eventually.of_forall fun t => (hcont _ f hf).aestronglyMeasurable)
    (Integrable.of_bound (hcont _ f hf).aestronglyMeasurable C (Filter.Eventually.of_forall (hnorm _ f hfC)))
    (hcont _ f' hf').aestronglyMeasurable
    (ae_of_all _ fun y t _ => hnorm _ f' hf'C y)
    (integrable_const C)
    (ae_of_all _ fun y t _ => (hM (x, y) t).mul_const _)
  have e : (fun y => heisV ψ (M 0) f' (x, y) * ψ (-(⅟(2 : AF F) * (x ⬝ᵥ y)))) =
      fun y => f' (x, y) * ψ (-(⅟(2 : AF F) * (x ⬝ᵥ y))) := by
    rw [map_zero, heisV_zero]
  have k2 := key.2
  simp only [e] at k2
  exact k2

end GlobalTheory.ThetaTransform
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat GlobalTheory.HomFixUniv

noncomputable section

namespace GlobalTheory.FormsLocus

theorem ΓSpecIso_inv_comp_specMap_appTop {W : Scheme.{0}} {A B : CommRingCat.{0}} (g : W ⟶ Spec B)
    (f : A ⟶ B) :
    (Scheme.ΓSpecIso A).inv ≫ (g ≫ Spec.map f).appTop =
      f ≫ (Scheme.ΓSpecIso B).inv ≫ g.appTop := by
  rw [Scheme.Hom.comp_appTop, ← Category.assoc, ← Category.assoc, Scheme.ΓSpecIso_inv_naturality]

theorem factors_quot_iff (Rg : Type) [CommRing Rg] (n : ℕ) (I : Ideal (MvPolynomial (Fin n) Rg))
    (T : Scheme.{0}) (g : T ⟶ Sp (MvPolynomial (Fin n) Rg)) :
    (∃ w : T ⟶ Sp (MvPolynomial (Fin n) Rg ⧸ I),
      w ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) = g) ↔
      ∀ P ∈ I, GlobalTheory.FormsLocus.ringOf g P = 0 := by
  constructor
  · rintro ⟨w, rfl⟩ P hP
    have h := congrArg (fun k => k.hom P)
      (ΓSpecIso_inv_comp_specMap_appTop w (CommRingCat.ofHom (Ideal.Quotient.mk I)))
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h
    change ((w ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))).appTop.hom
      ((Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial (Fin n) Rg))).inv.hom P)) = 0
    rw [h, Ideal.Quotient.eq_zero_iff_mem.2 hP, map_zero, map_zero]
  · intro h
    let φ : CommRingCat.of (MvPolynomial (Fin n) Rg) ⟶ Γ(T, ⊤) :=
      (Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial (Fin n) Rg))).inv ≫ g.appTop
    refine ⟨T.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.lift I φ.hom h)), ?_⟩
    rw [Category.assoc, ← Spec.map_comp]
    change T.toSpecΓ ≫ Spec.map φ = g
    apply ext_of_isAffine
    rw [← cancel_epi (Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial (Fin n) Rg))).inv,
      ΓSpecIso_inv_comp_specMap_appTop, Scheme.toSpecΓ_appTop, Iso.inv_hom_id, Category.comp_id]

end GlobalTheory.FormsLocus
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat GlobalTheory.HomFixUniv

namespace GlobalTheory.FormsLocus.VecGerm

theorem gs_map_sum {Y X : Scheme.{0}} (φ : Y ⟶ X) (z : Y) (U : X.Opens) (h : φ z ∈ U) {κ : Type} (t : Finset κ)
    (a b : κ → Γ(X, U)) : gs φ z U (∑ k ∈ t, a k * b k) = ∑ k ∈ t, gs φ z U (a k) * gs φ z U (b k) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [gs_eq φ z U h, map_sum, map_mul]

theorem germ_eq_sum_vecOf : ∀ (Rg : Type) [CommRing Rg] (A₀ X : Scheme.{0}) (f : A₀ ⟶ Sp Rg) (M : LB A₀) (Q : GlobalTheory.AbLaw.Perf f M) (s : LB.Sec M) (φ : X ⟶ A₀) (z : X) (i : Q.I), φ z ∈ Q.W i → gs φ z (M.U (Q.ch i)) (s.f (Q.ch i)) = ∑ k, gs φ z ⊤ (GlobalTheory.FormsLocus.cstT f (GlobalTheory.FormsLocus.vecOf Q s k)) * gs φ z (Q.W i) (Q.u k i) := by
  intro Rg _ A₀ X f M Q s φ z i hz
  have h := vecOf_spec Q s i
  have hz' : φ z ∈ (𝟙 A₀) ⁻¹ᵁ Q.W i := hz
  have h2 := congrArg (gs φ z ((𝟙 A₀) ⁻¹ᵁ Q.W i)) h
  rw [gs_map_sum φ z _ hz'] at h2
  have hl : gs φ z ((𝟙 A₀) ⁻¹ᵁ Q.W i) (GlobalTheory.AbLaw.rs A₀ (GlobalTheory.AbLaw.le_pull M (𝟙 A₀) (Q.le i))
      ((GlobalTheory.AbLaw.finSecPullId s).f (fun _ => Q.ch i))) = gs φ z (M.U (Q.ch i)) (s.f (Q.ch i)) := by
    unfold GlobalTheory.AbLaw.finSecPullId
    dsimp only
    exact (gs_res φ z _ hz' _).trans (gs_res φ z _ (GlobalTheory.AbLaw.le_pull M (𝟙 A₀) (Q.le i) hz') _)
  rw [hl] at h2
  rw [h2]
  refine Finset.sum_congr rfl fun k _ => ?_
  congr 1
  · show gs φ z _ ((A₀.presheaf.map (homOfLE le_top).op).hom (cstT f (vecOf Q s k))) = _
    exact gs_res φ z le_top hz' _

end GlobalTheory.FormsLocus.VecGerm
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat GlobalTheory.HomFixUniv

namespace GlobalTheory.FormsLocus

theorem cstT_comp_affπ {Rg : Type} [CommRing Rg] {T : Scheme.{0}} {n : ℕ}
    (g : T ⟶ Sp (MvPolynomial (Fin n) Rg)) (r : Rg) :
    cstT (g ≫ affπ Rg n) r = ringOf g (MvPolynomial.C r) := by
  have n2 : (Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial (Fin n) Rg))).inv (MvPolynomial.C r) =
      (affπ Rg n).appTop ((Scheme.ΓSpecIso (CommRingCat.of Rg)).inv r) := by
    rw [← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_inv_naturality]; rfl
  simp only [cstT, ringOf, RingHom.coe_comp, Function.comp_apply, Scheme.Hom.comp_appTop, CommRingCat.hom_comp]
  rw [n2]

theorem polys_ker : ∀ (Rg : Type) [CommRing Rg] (A₀ T : Scheme.{0}) (f : A₀ ⟶ Sp Rg) (N : LB A₀) (mA mB : ℕ) (Q : ∀ d : ℕ, GlobalTheory.AbLaw.Perf f (GlobalTheory.AbLaw.pw N (d : ℤ))) (a : Fin mA → LB.Sec N) (g : T ⟶ Sp (MvPolynomial (Fin (mA * mB)) Rg)) (d : ℕ) (F : MvPolynomial (Fin mB) Rg), ((Q d).D₀.map (GlobalTheory.FormsLocus.cstT (g ≫ affπ Rg (mA * mB)))).mulVec (fun k => GlobalTheory.FormsLocus.ringOf g (GlobalTheory.FormsLocus.polys Q a d F k)) = 0 := by
  intro Rg _ A₀ T f N mA mB Q a g d F
  have hC : ((Q d).D₀.map MvPolynomial.C).mulVec (fun k => polys Q a d F k) = 0 := by
    funext l
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, polys, Finset.mul_sum, Pi.zero_apply]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun ν _ => ?_
    have h0 := congrFun (vecOf_ker (Q d) (monSec a d ν)) l
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, RingHom.id_apply, Pi.zero_apply] at h0
    calc ∑ k, MvPolynomial.C ((Q d).D₀ l k) * ((expand mA mB F).coeff ν * MvPolynomial.C (vecOf (Q d) (monSec a d ν) k))
        = (expand mA mB F).coeff ν * MvPolynomial.C (∑ k, (Q d).D₀ l k * vecOf (Q d) (monSec a d ν) k) := by

          rw [map_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [map_mul]; ring
      _ = 0 := by rw [h0, map_zero, mul_zero]
  have hm : (Q d).D₀.map (cstT (g ≫ affπ Rg (mA * mB))) = ((Q d).D₀.map MvPolynomial.C).map (ringOf g) := by
    rw [Matrix.map_map]; congr 1; funext r; exact cstT_comp_affπ g r
  rw [hm]
  funext l
  have e := RingHom.map_mulVec (ringOf g) ((Q d).D₀.map MvPolynomial.C) (fun k => polys Q a d F k) l
  rw [hC] at e
  simp only [Pi.zero_apply, map_zero] at e
  exact e.symm

end GlobalTheory.FormsLocus
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat GlobalTheory.HomFixUniv

noncomputable section

namespace GlobalTheory.FormsLocus

theorem germ_cstT_eq_germ_ringOf_C : ∀ (Rg : Type) [CommRing Rg] (A₀ T X : Scheme.{0}) (f : A₀ ⟶ Sp Rg) (n : ℕ) (g : T ⟶ Sp (MvPolynomial (Fin n) Rg)) (φ : X ⟶ A₀) (p : X ⟶ T), φ ≫ f = p ≫ g ≫ affπ Rg n → ∀ (z : X) (r : Rg), gs φ z ⊤ (GlobalTheory.FormsLocus.cstT f r) = gs p z ⊤ (GlobalTheory.FormsLocus.ringOf g (MvPolynomial.C r)) := by
  intro Rg _ A₀ T X f n g φ p h z r
  have e0 : (affπ Rg n).appTop ((Scheme.ΓSpecIso (CommRingCat.of Rg)).inv r) =
      (Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial (Fin n) Rg))).inv (MvPolynomial.C r) := by
    rw [← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_inv_naturality]; rfl
  have e1 : gs φ z ⊤ (cstT f r) = gs (φ ≫ f) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of Rg)).inv r) :=
    gs_pull φ f z ⊤ trivial _
  have h1 := gs_pull (p ≫ g) (affπ Rg n) z ⊤ trivial ((Scheme.ΓSpecIso (CommRingCat.of Rg)).inv r)
  have h2 := gs_pull p g z ⊤ trivial
    ((Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial (Fin n) Rg))).inv (MvPolynomial.C r))
  rw [Category.assoc] at h1
  rw [e1, h, ← h1]
  refine Eq.trans ?_ h2.symm
  change gs (p ≫ g) z ⊤ ((affπ Rg n).appTop _) = _
  rw [e0]

end GlobalTheory.FormsLocus
end
end

section

namespace GlobalTheory.MulVecZeroDenominator

private lemma mulVec_eq_zero_of_map_mulVec_eq_zero {O L : Type} [CommRing O] [IsDomain O] [Field L] [Algebra O L]
    [IsFractionRing O L] {m c : ℕ} (D : Matrix (Fin m) (Fin c) O) (x : Fin c → L) (v : Fin c → O)
    (d : O) (hv : ∀ i, algebraMap O L (v i) = d • x i)
    (hD : Matrix.mulVec (Matrix.map D (algebraMap O L)) x = 0) : Matrix.mulVec D v = 0 := by
  funext i
  apply IsFractionRing.injective O L
  rw [RingHom.map_mulVec, Pi.zero_apply, map_zero]
  have hvx : (algebraMap O L ∘ v) = d • x := funext hv
  rw [hvx, Matrix.mulVec_smul, hD, smul_zero, Pi.zero_apply]

private lemma exists_common_denominator_divisor {O L : Type} [CommRing O] [IsDomain O] [Field L] [Algebra O L]
    [IsFractionRing O L] {c : ℕ} (x : Fin c → L) :
    ∃ (d : O) (v : Fin c → O), algebraMap O L d ≠ 0 ∧ ∀ i, algebraMap O L (v i) = d • x i := by
  obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors O) x
  choose v hv using hd
  exact ⟨d, v, IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors d.2, hv⟩

theorem target : ∀ {O L : Type} [inst : CommRing O] [IsDomain O] [inst_2 : Field L] [inst_3 : Algebra O L] [IsFractionRing O L] {a b c : ℕ} (B : GlobalTheory.WachPlace.Mx O a c) (C : GlobalTheory.WachPlace.Mx O b c), (∀ (v : Fin c → O), Matrix.mulVec B v = (0 : Fin a → O) → Matrix.mulVec C v = (0 : Fin b → O) → v = (0 : Fin c → O)) → ∀ (x : Fin c → L), Matrix.mulVec (Matrix.map B (⇑(Algebra.algebraMap O L) : O → L)) x = (0 : Fin a → L) → Matrix.mulVec (Matrix.map C (⇑(Algebra.algebraMap O L) : O → L)) x = (0 : Fin b → L) → x = (0 : Fin c → L) := by
  intro O L _ _ _ _ _ a b c B C h x hB hC
  obtain ⟨d, v, hd, hv⟩ := exists_common_denominator_divisor (O := O) x
  have hv0 : v = 0 := h v (mulVec_eq_zero_of_map_mulVec_eq_zero B x v d hv hB) (mulVec_eq_zero_of_map_mulVec_eq_zero C x v d hv hC)
  funext i
  have hi := hv i
  rw [hv0, Pi.zero_apply, map_zero, Algebra.smul_def] at hi
  exact (mul_eq_zero.mp hi.symm).resolve_left hd

end GlobalTheory.MulVecZeroDenominator
end

section

open Classical GlobalTheory.FinWeil
open scoped BigOperators

theorem _root_.GlobalTheory.T.exists_weil_representation_of_lattice_vacua : ∀ {R X M : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M] {σ : R →+* R} {w : R} {γ : X → X → ℂ} {W : X → M →ₗ[ℂ] M}, IsHeis σ w γ W → ∀ lam : ℕ →* ℂ, GoodNorm σ lam → ∀ A : Submodule R X, SelfDual γ A → Submodule.span ℂ {m : M | ∃ x e, Fixes W A e ∧ m = W x e} = ⊤ → ∀ {Γ : Type} [Group Γ] (ρ : Γ →* Module.End R X), (∀ g x y, γ (ρ g x) (ρ g y) = γ x y) → (∀ g, idx A (A.map (ρ g)) ≠ 0) → ∃ Om : Γ →* Module.End ℂ M, (∀ g x v, Om g (W x v) = W (ρ g x) (Om g v)) ∧ ∀ g, SelfDual γ (A.map (ρ g)) ∧ ∀ e, Fixes W A e → Om g e = normOp lam W A (A.map (ρ g)) e := by
  first | exact @GlobalTheory.FinWeil.exists_weil_rep_of_vacua | exact GlobalTheory.FinWeil.exists_weil_rep_of_vacua | (intros; apply GlobalTheory.FinWeil.exists_weil_rep_of_vacua <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up
open scoped ENNReal

theorem _root_.GlobalTheory.T.lie_lattice_dual_index : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (G : Matrix (Fin r) (Fin r) E) (Λ : Submodule (𝓞 E) (Fin r → E)), 2 ≤ r → Unr E → SelfDualLat G Λ → (lieLat G Λ).relIndex (AddSubgroup.closure {Y : Matrix (Fin r) (Fin r) E | Y.trace = 0 ∧ (∀ u w, herm G (Y *ᵥ u) w + herm G u (Y *ᵥ w) = 0) ∧ ∀ X ∈ lieLat G Λ, IsIntegral ℤ (Matrix.trace (X * Y))}) = r ^ fdeg E := by
  first | exact @GlobalTheory.lieLat_relIndex_dual | exact GlobalTheory.lieLat_relIndex_dual | (intros; apply GlobalTheory.lieLat_relIndex_dual <;> assumption)
end
