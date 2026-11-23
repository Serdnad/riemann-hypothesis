module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle009
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.ExistsEtaleCoordsVanishing
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle007
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle011
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TopLePreimageOfValAtNeZero
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TangentBijectionOfValues
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle018
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle010
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle029
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SymplecticTorsionSystemIsGeometricBasis
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle001
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle003

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

noncomputable section

namespace GlobalTheory.SubfieldChart


open Filter Topology in
theorem exists_finite_test {A : Type} {e : A → ℂ} {N : Set (A → ℂ)} (hN : N ∈ 𝓝 e) :
    ∃ (n : ℕ) (r : Fin n → A) (ε : ℝ), 0 < ε ∧ ∀ u : A → ℂ, (∀ i, ‖u (r i) - e (r i)‖ < ε) → u ∈ N := by
  rw [nhds_pi, Filter.mem_pi] at hN
  obtain ⟨I, hI, t, ht, hsub⟩ := hN
  obtain ⟨n, r, hr⟩ := hI.fin_param
  have h1 : Set.pi Set.univ (fun i => t (r i)) ∈ 𝓝 (fun i => e (r i)) :=
    set_pi_mem_nhds Set.finite_univ fun i _ => ht (r i)
  obtain ⟨ε, hε, hb⟩ := Metric.mem_nhds_iff.1 h1
  refine ⟨n, r, ε, hε, fun u hu => hsub fun a ha => ?_⟩
  rw [← hr.2] at ha
  obtain ⟨i, rfl⟩ := ha
  refine hb (a := fun i => u (r i)) ?_ i trivial
  rw [Metric.mem_ball, dist_pi_lt_iff hε]
  intro j
  rw [dist_eq_norm]
  exact hu j

section Ring

variable {k A : Type} [Field k] [Algebra k ℂ] [CommRing A] [Algebra k A]

def extPt (x : A →ₐ[k] ℂ) : ℂ ⊗[k] A →ₐ[ℂ] ℂ :=
  Algebra.TensorProduct.lift (AlgHom.id ℂ ℂ) x fun _ _ => Commute.all _ _

def resPt (z : ℂ ⊗[k] A →ₐ[ℂ] ℂ) : A →ₐ[k] ℂ :=
  (z.restrictScalars k).comp Algebra.TensorProduct.includeRight

theorem extPt_tmul (x : A →ₐ[k] ℂ) (c : ℂ) (a : A) : extPt x (c ⊗ₜ a) = c * x a := by
  simp [extPt]

theorem resPt_apply (z : ℂ ⊗[k] A →ₐ[ℂ] ℂ) (a : A) : resPt z a = z (1 ⊗ₜ a) := rfl

theorem resPt_extPt (x : A →ₐ[k] ℂ) : resPt (extPt x) = x := by
  ext a
  rw [resPt_apply, extPt_tmul, _root_.one_mul]

theorem extPt_resPt (z : ℂ ⊗[k] A →ₐ[ℂ] ℂ) : extPt (resPt z) = z := by
  ext a
  simp [extPt_tmul, resPt_apply]

theorem exists_continuous_extPt (t : ℂ ⊗[k] A) :
    ∃ F : (A → ℂ) → ℂ, Continuous F ∧ ∀ x : A →ₐ[k] ℂ, F x = extPt x t := by
  induction t using TensorProduct.induction_on with
  | zero => exact ⟨fun _ => 0, continuous_const, fun x => by simp⟩
  | tmul c a => exact ⟨fun u => c * u a, by fun_prop, fun x => (extPt_tmul x c a).symm⟩
  | add s t hs ht =>
    obtain ⟨F, hF, hF'⟩ := hs
    obtain ⟨G, hG, hG'⟩ := ht
    exact ⟨fun u => F u + G u, hF.add hG, fun x => by simp [hF', hG']⟩

theorem exists_chart_algebra (d : ℕ) [Algebra.IsStandardSmoothOfRelativeDimension d k A]
    (e : A →ₐ[k] ℂ) :
    ∃ (W : Set (Fin d → ℂ)) (p : (Fin d → ℂ) → (A →ₐ[k] ℂ)) (n : ℕ) (r : Fin n → A) (ε : ℝ),
      IsOpen W ∧ 0 ∈ W ∧ p 0 = e ∧ 0 < ε ∧ (∀ a, DifferentiableOn ℂ (fun w => p w a) W) ∧
      Set.InjOn p W ∧ ∀ x : A →ₐ[k] ℂ, (∀ i, ‖x (r i) - e (r i)‖ < ε) → ∃ w ∈ W, x = p w := by
  have hc : (algebraMap ℂ (ℂ ⊗[k] A)).IsStandardSmoothOfRelativeDimension d :=
    (RingHom.isStandardSmoothOfRelativeDimension_algebraMap d).2 inferInstance
  obtain ⟨φ, hφc, hφ, hφ0⟩ := HolChart.exists_etale_coords_vanishing _ hc (extPt e).toRingHom
    (fun a => (extPt e).commutes a)
  let _ : Algebra (MvPolynomial (Fin d) ℂ) (ℂ ⊗[k] A) := φ.toAlgebra
  have _ : IsScalarTower ℂ (MvPolynomial (Fin d) ℂ) (ℂ ⊗[k] A) :=
    IsScalarTower.of_algebraMap_eq' hφc.symm
  have _ : Algebra.Etale (MvPolynomial (Fin d) ℂ) (ℂ ⊗[k] A) := hφ
  obtain ⟨W, σ, n, f, ε, hW, hW0, hσ0, hε, hσd, hσt, hσs⟩ :=
    exists_holomorphic_section_of_etale d (ℂ ⊗[k] A) (extPt e) hφ0
  choose F hF hF' using fun j => exists_continuous_extPt (f j)
  have hN : {u : A → ℂ | ∀ j, ‖F j u - extPt e (f j)‖ < ε} ∈ nhds (e : A → ℂ) := by
    refine IsOpen.mem_nhds ?_ fun j => ?_
    · rw [Set.setOf_forall]
      exact isOpen_iInter_of_finite fun j =>
        isOpen_lt (((hF j).sub continuous_const).norm) continuous_const
    · rw [hF', sub_self, norm_zero]; exact hε
  obtain ⟨m, r, δ, hδ, hr⟩ := exists_finite_test hN
  refine ⟨W, fun w => resPt (σ w), m, r, δ, hW, hW0, ?_, hδ, fun a => hσd (1 ⊗ₜ a), ?_, ?_⟩
  · show resPt (σ 0) = e
    rw [hσ0, resPt_extPt]
  · intro w hw w' hw' h
    have h1 : σ w = σ w' := by
      rw [← extPt_resPt (σ w), ← extPt_resPt (σ w')]
      exact congrArg extPt h
    funext i
    rw [← hσt w hw i, h1, hσt w' hw' i]
  · intro x hx
    obtain ⟨w, hw, h⟩ := hσs (extPt x) fun j => by
      rw [← hF']; exact hr x hx j
    exact ⟨w, hw, (resPt_extPt x).symm.trans (congrArg resPt h)⟩

end Ring

theorem exists_holomorphic_chart :
    ∀ (k : Type) [Field k] (σ : k →+* ℂ) (X : Scheme.{0}) (s : X ⟶ Sp k) (d : ℕ) (y₀ : Sp ℂ ⟶ X), SmoothOfRelativeDimension d s → y₀ ≫ s = spMap σ → ∃ (B : Set (Fin d → ℂ)) (y : (Fin d → ℂ) → (Sp ℂ ⟶ X)) (U : X.Opens) (f : Fin d → Γ(X, U)) (n : ℕ) (r : Fin n → Γ(X, U)), IsOpen B ∧ (0 : Fin d → ℂ) ∈ B ∧ y 0 = y₀ ∧ (∀ b ∈ B, y b ≫ s = spMap σ) ∧ IsHolTo B y ∧ Set.InjOn y B ∧ ⊤ ≤ y₀ ⁻¹ᵁ U ∧ ∃ ε : ℝ, 0 < ε ∧ ∀ x : Sp ℂ ⟶ X, x ≫ s = spMap σ → ⊤ ≤ x ⁻¹ᵁ U → (∀ i, ‖valAt' x U (r i) - valAt' y₀ U (r i)‖ < ε) → x ∈ y '' B := by
  intro k _ σ X s d y₀ hX hy₀
  obtain ⟨U₀, -, U, hU, hp, hle, hsm⟩ :=
    hX.exists_isStandardSmoothOfRelativeDimension (y₀ (default : PrimeSpectrum ℂ))
  have hU₀ : U₀ = ⊤ := by
    refine eq_top_iff.2 fun y _ => ?_
    have h1 : s (y₀ (default : PrimeSpectrum ℂ)) ∈ U₀ := hle hp
    have h2 : y = s (y₀ (default : PrimeSpectrum ℂ)) :=
      Subsingleton.elim (α := PrimeSpectrum k) _ _
    rw [h2]; exact h1
  subst hU₀
  let c : k →+* Γ(X, U) :=
    (s.appLE ⊤ U hle).hom.comp (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom
  have hc : c.IsStandardSmoothOfRelativeDimension d :=
    RingHom.isStandardSmoothOfRelativeDimension_respectsIso.2 (s.appLE ⊤ U hle).hom
      (Scheme.ΓSpecIso (CommRingCat.of k)).symm.commRingCatIsoToRingEquiv hsm
  let _ : Algebra k ℂ := σ.toAlgebra
  let _ : Algebra k Γ(X, U) := c.toAlgebra
  have _ : Algebra.IsStandardSmoothOfRelativeDimension d k Γ(X, U) := hc
  let pt : (Γ(X, U) →+* ℂ) → (Sp ℂ ⟶ X) := fun e =>
    Spec.map (CommRingCat.ofHom e : Γ(X, U) ⟶ CommRingCat.of ℂ) ≫ hU.fromSpec
  have hptU : ∀ e, ⊤ ≤ pt e ⁻¹ᵁ U := fun e p _ => hU.range_fromSpec.le ⟨_, rfl⟩
  have hptv : ∀ e f, valAt' (pt e) U f = e f := fun e f => by
    rw [valAt', dite_eq_left (hptU e)]
    exact congrArg (fun ψ => ψ.hom f)
      (AffinePointValues.appLE_specMap_fromSpec hU (CommRingCat.ofHom e) (hptU e))
  have hpts : ∀ e, pt e ≫ s = spMap (e.comp c) := fun e => by
    simp only [pt]
    rw [Category.assoc, AffinePointValues.fromSpec_comp hU s hle, ← Spec.map_comp]
    rfl
  have hsurj : ∀ x : Sp ℂ ⟶ X, x ≫ s = spMap σ → ⊤ ≤ x ⁻¹ᵁ U →
      ∃ e : Γ(X, U) →ₐ[k] ℂ, pt e.toRingHom = x := by
    intro x hxs hx
    let e : Γ(X, U) →+* ℂ := (x.appLE U ⊤ hx ≫ (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom).hom
    have he : pt e = x := AffinePointValues.specMap_appLE_fromSpec hU (R := CommRingCat.of ℂ) x hx
    have h1 : spMap (e.comp c) = spMap σ := by rw [← hpts, he, hxs]
    have h2 : e.comp c = σ := congrArg CommRingCat.Hom.hom (Spec.map_injective h1)
    exact ⟨{ e with commutes' := fun a => RingHom.congr_fun h2 a }, he⟩
  have hyU : ⊤ ≤ y₀ ⁻¹ᵁ U := ((valAt'_rules X y₀).1 U).2 hp
  obtain ⟨e, rfl⟩ := hsurj y₀ hy₀ hyU
  obtain ⟨W, p, n, r, ε, hW, hW0, hp0, hε, hpd, hpi, hps⟩ := exists_chart_algebra d e
  refine ⟨W, fun w => pt (p w).toRingHom, U, fun _ => 0, n, r, hW, hW0, by simp only [hp0],
    fun b _ => ?_, fun V f => ?_, fun w hw w' hw' h => hpi hw hw' ?_, hyU, ε, hε,
    fun x hxs hx hxe => ?_⟩
  · rw [hpts]
    congr 2
    exact RingHom.ext fun a => (p b).commutes a
  · exact HolChart.hol_of_affine valAt'_rules hU hW (fun w => pt (p w).toRingHom)
      (fun w _ => hptU _) (fun a => (hpd a).congr fun w _ => hptv _ a) V f
  · refine AlgHom.ext fun a => ?_
    have h1 := hptv (p w).toRingHom a
    have h' : pt (p w).toRingHom = pt (p w').toRingHom := h
    rw [h', hptv] at h1
    exact h1.symm
  · obtain ⟨e', rfl⟩ := hsurj x hxs hx
    obtain ⟨w, hw, h⟩ := hps e' fun i => by
      have := hxe i
      rw [hptv, hptv] at this
      exact this
    exact ⟨w, hw, by rw [h]⟩

end GlobalTheory.SubfieldChart
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

noncomputable section

namespace GlobalTheory.PointUnif

section Deriv

open GlobalTheory.TangentOrigin GlobalTheory.LieEtale

variable {g g' : ℕ} {X Y : Scheme.{0}}

theorem evalPt_comp {R : Type} [CommRing R] (x : Sp R ⟶ X) (φ : X ⟶ Y) (U : Y.Opens)
    (h : ⊤ ≤ (x ≫ φ) ⁻¹ᵁ U) (f : Γ(Y, U)) :
    evalPt (x ≫ φ) U h f = evalPt x (φ ⁻¹ᵁ U) h ((φ.app U).hom f) := by
  have := Scheme.Hom.appLE_comp_appLE x φ U (φ ⁻¹ᵁ U) ⊤ le_rfl h
  unfold evalPt
  rw [← this, Scheme.Hom.app_eq_appLE]
  rfl

theorem valAt'_comp (x : Sp ℂ ⟶ X) (φ : X ⟶ Y) (U : Y.Opens) (f : Γ(Y, U)) :
    valAt' (x ≫ φ) U f = valAt' x (φ ⁻¹ᵁ U) ((φ.app U).hom f) := by
  by_cases h : ⊤ ≤ (x ≫ φ) ⁻¹ᵁ U
  · rw [valAt'_eq_evalPt _ _ h, valAt'_eq_evalPt x (φ ⁻¹ᵁ U) h, evalPt_comp]
  · have h' : ¬ ⊤ ≤ x ⁻¹ᵁ φ ⁻¹ᵁ U := h
    unfold valAt'
    rw [dite_eq_right h, dite_eq_right h']

theorem isHolTo_comp {e : (Fin g → ℂ) → (Sp ℂ ⟶ X)} (he : IsHolTo Set.univ e) (φ : X ⟶ Y) :
    IsHolTo Set.univ fun z => e z ≫ φ := by
  intro U f
  simp only [valAt'_comp]
  exact he (φ ⁻¹ᵁ U) ((φ.app U).hom f)

theorem isHolTo_linear {e : (Fin g → ℂ) → (Sp ℂ ⟶ X)} (he : IsHolTo Set.univ e)
    (F : (Fin g' → ℂ) →ₗ[ℂ] (Fin g → ℂ)) : IsHolTo Set.univ fun z => e (F z) := by
  intro U f
  have hF : Differentiable ℂ F := F.toContinuousLinearMap.differentiable
  exact ⟨(he U f).1.preimage hF.continuous, (he U f).2.comp hF.differentiableOn fun z hz => hz⟩

theorem isDerivAt0_iff {e : (Fin g → ℂ) → (Sp ℂ ⟶ X)} {w : Fin g → ℂ} {v : Sp (DualNumber ℂ) ⟶ X} :
    IsDerivAt0 e w v ↔ spMap fstC ≫ v = e 0 ∧ ∀ (U : X.Opens) (h : ⊤ ≤ v ⁻¹ᵁ U) (f : Γ(X, U)),
      (evalPt v U h f).snd = fderiv ℂ (fun z => valAt' (e z) U f) 0 w := Iff.rfl

theorem deriv_comp {e : (Fin g → ℂ) → (Sp ℂ ⟶ X)} {w : Fin g → ℂ} {v : Sp (DualNumber ℂ) ⟶ X}
    (h : IsDerivAt0 e w v) (φ : X ⟶ Y) : IsDerivAt0 (fun z => e z ≫ φ) w (v ≫ φ) := by
  rw [isDerivAt0_iff] at h ⊢
  refine ⟨by rw [← h.1, Category.assoc], fun U hU f => ?_⟩
  simp only [valAt'_comp]
  rw [evalPt_comp]
  exact h.2 _ _ _

theorem deriv_unique {e : (Fin g → ℂ) → (Sp ℂ ⟶ X)} {w : Fin g → ℂ} {v v' : Sp (DualNumber ℂ) ⟶ X}
    (h : IsDerivAt0 e w v) (h' : IsDerivAt0 e w v') : v = v' := by
  rw [isDerivAt0_iff] at h h'
  obtain ⟨_, ⟨U, hU, rfl⟩, hx, -⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (e 0 (default : PrimeSpectrum ℂ))) isOpen_univ
  have h0 : ⊤ ≤ e 0 ⁻¹ᵁ U := fun q _ => by
    rw [Subsingleton.elim (α := PrimeSpectrum ℂ) q default]; exact hx
  have hv : ⊤ ≤ v ⁻¹ᵁ U := (top_le_preimage_iff v U).2 (h.1 ▸ h0)
  have hv' : ⊤ ≤ v' ⁻¹ᵁ U := (top_le_preimage_iff v' U).2 (h'.1 ▸ h0)
  refine ext_evalPt hU hv hv' (RingHom.ext fun f => TrivSqZeroExt.ext ?_ ((h.2 U hv f).trans (h'.2 U hv' f).symm))
  have key : ∀ (u : Sp (DualNumber ℂ) ⟶ X) (hu : ⊤ ≤ u ⁻¹ᵁ U) (y : Sp ℂ ⟶ X) (hy : ⊤ ≤ y ⁻¹ᵁ U),
      spMap fstC ≫ u = y → (evalPt u U hu f).fst = evalPt y U hy f := by
    rintro u hu y hy rfl
    exact (evalPt_spMap_comp fstC u U hu hy f).symm
  exact (key v hv _ h0 h.1).trans (key v' hv' _ h0 h'.1).symm

theorem deriv_linear {e : (Fin g → ℂ) → (Sp ℂ ⟶ X)} (he : IsHolTo Set.univ e)
    (F : (Fin g' → ℂ) →ₗ[ℂ] (Fin g → ℂ)) {w : Fin g' → ℂ} {v : Sp (DualNumber ℂ) ⟶ X} :
    IsDerivAt0 (fun z => e (F z)) w v ↔ IsDerivAt0 e (F w) v := by
  rw [isDerivAt0_iff, isDerivAt0_iff, map_zero]
  refine and_congr_right fun h0 => forall₃_congr fun U hU f => ?_
  have hU0 : ⊤ ≤ e 0 ⁻¹ᵁ U := h0 ▸ (top_le_preimage_iff v U).1 hU
  have hd : DifferentiableAt ℂ (fun z => valAt' (e z) U f) (F.toContinuousLinearMap 0) := by
    rw [map_zero]
    exact (he U f).2.differentiableAt ((he U f).1.mem_nhds ⟨trivial, hU0⟩)
  have := (hd.hasFDerivAt.comp 0 F.toContinuousLinearMap.hasFDerivAt).fderiv
  rw [map_zero] at this
  have e2 : fderiv ℂ (fun z => valAt' (e (F z)) U f) 0 = _ := this
  rw [e2]
  rfl

theorem deriv_smul {e : (Fin g → ℂ) → (Sp ℂ ⟶ X)} {w : Fin g → ℂ} {v : Sp (DualNumber ℂ) ⟶ X}
    (h : IsDerivAt0 e w v) (c : ℂ) : IsDerivAt0 e (c • w) (spMap (epsScale c) ≫ v) := by
  rw [isDerivAt0_iff] at h ⊢
  have e0 : spMap fstC ≫ spMap (epsScale c) ≫ v = spMap fstC ≫ v := by
    rw [← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp]
    congr 3
    exact RingHom.ext fun r => TrivSqZeroExt.fst_map _ r
  refine ⟨e0.trans h.1, fun U hU f => ?_⟩
  have hv : ⊤ ≤ v ⁻¹ᵁ U := (top_le_preimage_iff v U).2 (e0 ▸ (top_le_preimage_iff _ U).1 hU)
  rw [evalPt_spMap_comp _ v U hv hU, map_smul, ← h.2 U hv f]
  simp [epsScale]

variable {S : Scheme.{0}} {G : Over S} [GrpObj G] {y : Sp ℂ ⟶ S}

abbrev epsTwo (y : Sp ℂ ⟶ S) : Over S := Over.mk (spMap (algebraMap ℂ (TrivSqZeroExt ℂ (ℂ × ℂ))) ≫ y)

def toTwo (y : Sp ℂ ⟶ S) (l : ℂ →ₗ[ℂ] ℂ × ℂ) : epsTwo y ⟶ epsPt y :=
  Over.homMk (spMap (TrivSqZeroExt.map l).toRingHom) (by
    change _ ≫ _ ≫ y = _ ≫ y
    rw [← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp]
    congr 3
    exact RingHom.ext fun r => (TrivSqZeroExt.map l).commutes r)

def ofTwo (y : Sp ℂ ⟶ S) (l : ℂ × ℂ →ₗ[ℂ] ℂ) : epsPt y ⟶ epsTwo y :=
  Over.homMk (spMap (TrivSqZeroExt.map l).toRingHom) (by
    change _ ≫ _ ≫ y = _ ≫ y
    rw [← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp]
    congr 3
    exact RingHom.ext fun r => (TrivSqZeroExt.map l).commutes r)

theorem ofTwo_toTwo (l : ℂ →ₗ[ℂ] ℂ × ℂ) (l' : ℂ × ℂ →ₗ[ℂ] ℂ) :
    ofTwo y l' ≫ toTwo y l = epsPtScale y (l' (l 1)) := by
  refine Over.OverMorphism.ext ?_
  change spMap _ ≫ spMap _ = spMap _
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  refine RingHom.ext fun x => ?_
  have : l' (l x.snd) = l' (l 1) * x.snd := by
    rw [mul_comm, ← smul_eq_mul, ← map_smul, ← map_smul, smul_eq_mul, _root_.mul_one]
  ext <;> simp [this, epsScale]

theorem epsPtScale_one : epsPtScale y 1 = 𝟙 _ := by
  refine Over.OverMorphism.ext ?_
  change spMap _ = 𝟙 _
  rw [← Spec.map_id]
  congr 1
  ext x <;> simp [epsScale]

theorem epsPtScale_zero {v : epsPt y ⟶ G} (hv : epsPtZero y ≫ v = 1) : epsPtScale y 0 ≫ v = 1 := by
  let s : epsPt y ⟶ Over.mk y := Over.homMk (spMap (algebraMap ℂ (DualNumber ℂ))) rfl
  have : epsPtScale y 0 = s ≫ epsPtZero y := by
    refine Over.OverMorphism.ext ?_
    change spMap _ = spMap _ ≫ spMap _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    refine RingHom.ext fun x => ?_
    ext <;> simp [epsScale, TrivSqZeroExt.algebraMap_eq_inl]
  rw [this, Category.assoc, hv, MonObj.comp_one]

theorem deriv_mul {e : (Fin g → ℂ) → (Sp ℂ ⟶ G.left)} {w w' : Fin g → ℂ} {v v' : epsPt y ⟶ G}
    (h0 : e 0 = (1 : Over.mk y ⟶ G).left)
    (h : IsDerivAt0 e w v.left) (h' : IsDerivAt0 e w' v'.left) : IsDerivAt0 e (w + w') (v * v').left := by
  have hv : epsPtZero y ≫ v = 1 := Over.OverMorphism.ext (h.1.trans h0)
  have hv' : epsPtZero y ≫ v' = 1 := Over.OverMorphism.ext (h'.1.trans h0)
  have hm : epsPtZero y ≫ (v * v') = 1 := by rw [MonObj.comp_mul, hv, hv', _root_.mul_one]
  have hm' : spMap fstC ≫ (v * v').left = e 0 := (congrArg (·.left) hm).trans h0.symm
  rw [isDerivAt0_iff] at h h' ⊢
  refine ⟨hm', fun U hU f => ?_⟩
  let u : epsTwo y ⟶ G := (toTwo y (LinearMap.inl ℂ ℂ ℂ) ≫ v) * (toTwo y (LinearMap.inr ℂ ℂ ℂ) ≫ v')
  have hu : ∀ l, ofTwo y l ≫ u = (epsPtScale y (l (1, 0)) ≫ v) * (epsPtScale y (l (0, 1)) ≫ v') := fun l => by
    simp only [u, MonObj.comp_mul, ← Category.assoc, ofTwo_toTwo]
    rfl
  have h1 : ofTwo y (LinearMap.fst ℂ ℂ ℂ) ≫ u = v := by
    rw [hu, LinearMap.fst_apply, LinearMap.fst_apply, epsPtScale_one, epsPtScale_zero hv', _root_.mul_one, Category.id_comp]
  have h2 : ofTwo y (LinearMap.snd ℂ ℂ ℂ) ≫ u = v' := by
    rw [hu, LinearMap.snd_apply, LinearMap.snd_apply, epsPtScale_one, epsPtScale_zero hv, _root_.one_mul, Category.id_comp]
  have h3 : ofTwo y (LinearMap.fst ℂ ℂ ℂ + LinearMap.snd ℂ ℂ ℂ) ≫ u = v * v' := by
    rw [hu]; simp [epsPtScale_one]
  have hU0 : ⊤ ≤ e 0 ⁻¹ᵁ U := hm' ▸ (top_le_preimage_iff _ U).1 hU
  have hU1 : ⊤ ≤ v.left ⁻¹ᵁ U := (top_le_preimage_iff _ U).2 (h.1 ▸ hU0)
  have hU2 : ⊤ ≤ v'.left ⁻¹ᵁ U := (top_le_preimage_iff _ U).2 (h'.1 ▸ hU0)
  have hsub : ∀ p q : PrimeSpectrum (TrivSqZeroExt ℂ (ℂ × ℂ)), p = q := by
    have k : ∀ z : PrimeSpectrum (TrivSqZeroExt ℂ (ℂ × ℂ)), ∀ a, a ∈ z.asIdeal ↔ a.fst = 0 := fun z a => by
      constructor
      · intro ha
        by_contra h0
        exact z.2.ne_top (z.asIdeal.eq_top_of_isUnit_mem ha (TrivSqZeroExt.isUnit_iff_isUnit_fst.2 (Ne.isUnit h0)))
      · intro ha
        refine z.2.mem_of_pow_mem 2 ?_
        rw [show a ^ 2 = 0 by ext <;> simp [pow_two, ha]]
        exact z.asIdeal.zero_mem
    intro p q
    ext a
    rw [k, k]
  have hUu : ⊤ ≤ u.left ⁻¹ᵁ U := fun p _ => by
    let q : (epsPt y).left := spMap fstC (default : PrimeSpectrum ℂ)
    have hq : v.left q ∈ U := hU1 (Set.mem_univ q)
    rw [← h1] at hq
    rw [hsub p ((ofTwo y (LinearMap.fst ℂ ℂ ℂ)).left q)]
    exact hq
  have key : ∀ (l : ℂ × ℂ →ₗ[ℂ] ℂ) (x : epsPt y ⟶ G) (hx : ⊤ ≤ x.left ⁻¹ᵁ U), ofTwo y l ≫ u = x →
      (evalPt (R := DualNumber ℂ) x.left U hx f).snd =
        l (evalPt (R := TrivSqZeroExt ℂ (ℂ × ℂ)) u.left U hUu f).snd := by
    rintro l x hx rfl
    exact (congrArg TrivSqZeroExt.snd (evalPt_spMap_comp (TrivSqZeroExt.map l).toRingHom u.left U hUu hx f)).trans
      (TrivSqZeroExt.snd_map _ _)
  rw [map_add (f := _), ← h.2 U hU1 f, ← h'.2 U hU2 f, key _ _ hU h3, key _ _ hU1 h1, key _ _ hU2 h2]
  rfl

end Deriv

end GlobalTheory.PointUnif
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.ZM GlobalTheory.KS

noncomputable section
namespace GlobalTheory.SharpRel

section
variable {S S' : Scheme.{0}} {f : S' ⟶ S} {A : Over S} {A' : Over S'}
  [GrpObj A] [GrpObj A'] {φ : A'.left ⟶ A.left}

theorem push_inj (h : IsGrpPullback A' A f φ) {T : Over S'} {x y : T ⟶ A'}
    (e : pushHom h T x = pushHom h T y) : x = y := by
  have hl : x.left ≫ φ = y.left ≫ φ := congrArg CommaMorphism.left e
  ext1
  exact h.1.hom_ext hl (by rw [Over.w x, Over.w y])

theorem push_comp (h : IsGrpPullback A' A f φ) {p : A ⟶ A} {p' : A' ⟶ A'}
    (e : p'.left ≫ φ = φ ≫ p.left) {T : Over S'} (x : T ⟶ A') :
    pushHom h T (x ≫ p') = pushHom h T x ≫ p := by
  ext1
  change (x ≫ p').left ≫ φ = (x.left ≫ φ) ≫ p.left
  rw [Over.comp_left, Category.assoc, Category.assoc, e]

end

end GlobalTheory.SharpRel
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
theorem _root_.GlobalTheory.T.exists_level_with_odd_prime_first_number : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (l : Level H), ∃ n : ℕ, n.Prime ∧ Odd n ∧ ∀ A₀ : ℕ, 0 < A₀ → ∃ l₀ l₂ : Level H, l₀.M = n ∧ l₀.A = A₀ ∧ l₀.Dvd l₂ ∧ l.Dvd l₂ := by
  first | exact @GlobalTheory.ZM.exists_prime_level | exact GlobalTheory.ZM.exists_prime_level | (intros; apply GlobalTheory.ZM.exists_prime_level <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
theorem _root_.GlobalTheory.T.symplectic_torsion_system_is_geometric_basis : Out.Laws → ∀ (K₀ : Type) [Field K₀] (P : Out.PolAV (Sp K₀)) (k : ℕ) (ze : K₀ˣ) (pt : Fin (2 * P.g) → (Out.baseOver (Sp K₀) ⟶ P.A)), (k : K₀) ≠ 0 → IsPrimitiveRoot ze k → (∀ i, pt i ^ k = 1) → (∀ i j, Out.WeilIs P.A P.L k (pt i) (pt j) (unitOn ze ^ Out.stdSymp P.g i j)) → ∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ Sp K₀) (y : Over.mk x ⟶ P.A), y ^ k = 1 → ∃! c : Fin (2 * P.g) → ZMod k, Out.linComb (fun i => (Over.homMk x (by simp) : Over.mk x ⟶ Out.baseOver (Sp K₀)) ≫ pt i) (fun i => (c i).val) = y := by
  first | exact @GlobalTheory.symplectic_system_torsion_basis | exact GlobalTheory.symplectic_system_torsion_basis | (intros; apply GlobalTheory.symplectic_system_torsion_basis <;> assumption)
end
