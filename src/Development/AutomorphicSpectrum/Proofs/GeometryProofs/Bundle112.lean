module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle002
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.ExistsHolomorphicChartAtPoint
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle013
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TopLePreimageOfValAtNeZero
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.TwTan
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle010
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle101
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle001
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle102
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.FieldTheory.PurelyInseparable.Exponent
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Tactic.TypeStar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem hol_polydisc_chart : ∀ (K : Type) [Field K] (σ : K →+* ℂ) (X : Scheme.{0}) (s : X ⟶ Sp K) (d : ℕ) (T : Set X), SmoothOfRelativeDimension d s → Geo.ResK.HasSncCoords s d T → ∀ (x : Sp ℂ ⟶ X) (W : X.Opens), x ≫ s = spMap σ → ⊤ ≤ x ⁻¹ᵁ W → ∃ (V : X.Opens) (hV : IsAffineOpen V) (a : ℕ) (ψ : (Fin d → ℂ) → (Γ(X, V) →+* ℂ)), V ≤ W ∧ a ≤ d ∧ IsHolPts (ball 0 1) ψ ∧ spMap (ψ 0) ≫ hV.fromSpec = x ∧ Set.InjOn ψ (ball 0 1) ∧ (∀ z ∈ ball (0 : Fin d → ℂ) 1, spMap (ψ z) ≫ hV.fromSpec ≫ s = spMap σ ∧ (centre (spMap (ψ z) ≫ hV.fromSpec) ∉ T ↔ z ∈ punct d a 1)) ∧ ∀ (m : ℕ) (B : Set (Fin m → ℂ)) (y : (Fin m → ℂ) → (Sp ℂ ⟶ X)), IsOpen B → IsHolTo B y → (∀ b ∈ B, y b ≫ s = spMap σ) → ∀ b₀ ∈ B, y b₀ = x → ∃ (ε : ℝ) (κ : (Fin m → ℂ) → (Fin d → ℂ)), 0 < ε ∧ ball b₀ ε ⊆ B ∧ DifferentiableOn ℂ κ (ball b₀ ε) ∧ κ b₀ = 0 ∧ ∀ b ∈ ball b₀ ε, κ b ∈ ball (0 : Fin d → ℂ) 1 ∧ y b = spMap (ψ (κ b)) ≫ hV.fromSpec :=
  @PositivityTheory.Xgn.exists_holomorphic_chart_at_point

end GlobalTheory.CompanionTheory.Ar.Flat
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Sl.FrameZero

theorem tmul_one_injective {L : Type} [Field L] [NumberField L] (σ : L →+* ℂ)
    (M : Type) [AddCommGroup M] [Module (𝓞 L) M] [Module.Projective (𝓞 L) M] (x : M)
    (h : (1 : ComplexAt σ) ⊗ₜ[𝓞 L] x = 0) : x = 0 := by
  have hinj : Function.Injective (Algebra.linearMap (𝓞 L) (ComplexAt σ)) := by
    intro a b hab
    have h1 : σ (a : L) = σ (b : L) := hab
    exact RingOfIntegers.coe_injective (σ.injective h1)
  have hr := Module.Flat.rTensor_preserves_injective_linearMap (M := M) _ hinj
  have h2 : (Algebra.linearMap (𝓞 L) (ComplexAt σ)).rTensor M ((1 : 𝓞 L) ⊗ₜ[𝓞 L] x) =
      (Algebra.linearMap (𝓞 L) (ComplexAt σ)).rTensor M 0 := by
    rw [LinearMap.rTensor_tmul, map_zero, Algebra.linearMap_apply, map_one, h]
  have h3 := hr h2
  have h4 := congrArg (TensorProduct.lid (𝓞 L) M) h3
  simpa using h4

theorem core_eq_zero {V : Type*} [AddCommGroup V] [Module ℂ V] (C : InnerProductSpace.Core ℂ V)
    (v : V) (h : (C.inner v v : ℂ).re = 0) : v = 0 := by
  apply C.definite
  have him : (C.inner v v : ℂ).im = 0 := by
    have h1 := C.conj_inner_symm v v
    have h2 := congrArg Complex.im h1
    simp only [Complex.conj_im] at h2
    linarith
  exact Complex.ext h him

theorem coord_ne_zero (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (L : Type)
    [Field L] [NumberField L] (D : PPData H L) (σ : L →+* ℂ) (a : D.Frame σ) (x : D.B.carrier)
    (c : Fin D.g → ℂ) (hlen : D.len σ x ^ 2 = Real.pi * (a.herm c c).re) (hx : x ≠ 0) : c ≠ 0 := by
  rintro rfl
  apply hx
  have hherm : a.herm 0 0 = 0 := by simp [ArchFrame.herm]
  rw [hherm, Complex.zero_re, mul_zero] at hlen
  have hl : D.len σ x = 0 := by simpa using hlen
  have hnn : 0 ≤ (((D.B.metric.form σ).inner ((1 : ComplexAt σ) ⊗ₜ[𝓞 L] x)
      ((1 : ComplexAt σ) ⊗ₜ[𝓞 L] x) : ℂ)).re :=
    (D.B.metric.form σ).re_inner_nonneg _
  have hle := Real.sqrt_eq_zero'.mp hl
  exact tmul_one_injective σ D.B.carrier x (core_eq_zero _ _ (le_antisymm hle hnn))

end GlobalTheory.CompanionTheory.Ar.Sl.FrameZero
end
end

section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Sl.Fac

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl

private theorem eq_of_sp_complex_pts (y y' : ↥(ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp ℂ)) : y = y' := by
  have e : ∀ p : PrimeSpectrum ℂ, p.asIdeal = ⊥ := fun p => Ideal.eq_bot_of_prime p.asIdeal
  exact PrimeSpectrum.ext (R := ℂ) ((e y).trans (e y').symm)

theorem fn_factor (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (P : RigLB G) (z : Sp ℂ ⟶ S) (g : ℕ)
    (a : ArchFrame P z g) (n : ℕ) (s : Out.H0 P.L n) (θ : (Fin g → ℂ) → ℂ) (hθ : a.IsFn s θ)
    (l : a.u.Λ) (w : Fin g → ℂ) :
    θ (w + l) = (a.χ l * Complex.exp (Real.pi * a.herm w l + Real.pi / 2 * a.herm l l)) ^ n * θ w := by
  obtain ⟨-, -, -, hfr⟩ := a.ah
  obtain ⟨x0⟩ : Nonempty ↥(ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp ℂ) :=
    ⟨(IsLocalRing.closedPoint ℂ : PrimeSpectrum ℂ)⟩
  obtain ⟨i, hi⟩ : ∃ i : P.L.ι, ⊤ ≤ (TopologicalSpace.Opens.map (a.pt w).base).obj (P.L.U i) := by
    have hx : (a.pt w).base x0 ∈ (⨆ j, P.L.U j) := by
      rw [P.isLB.cover]
      trivial
    obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
    refine ⟨j, fun y _ => ?_⟩
    rw [eq_of_sp_complex_pts y x0]
    exact hj
  have hz : ∀ v : Fin g → ℂ, ⊤ ≤ (TopologicalSpace.Opens.map (a.pt v).base).obj (P.L.U i) →
      ⊤ ≤ (TopologicalSpace.Opens.map (CategoryTheory.Over.Hom.left (a.u.ex v)).base).obj
        ((P.L.pull a.φ).U fun _ => i) := by
    intro v hv y hy
    exact Set.mem_iInter.2 fun _ => hv hy
  have hpt : a.pt (w + (l : Fin g → ℂ)) = a.pt w := by
    have h1 : a.u.ex (l : Fin g → ℂ) = 1 := (a.u.ker _).2 l.2
    change CategoryTheory.CategoryStruct.comp (CategoryTheory.Over.Hom.left (a.u.ex (w + (l : Fin g → ℂ)))) a.φ =
      CategoryTheory.CategoryStruct.comp (CategoryTheory.Over.Hom.left (a.u.ex w)) a.φ
    rw [a.u.ex_add, h1, _root_.mul_one]
  have hi' : ⊤ ≤ (TopologicalSpace.Opens.map (a.pt (w + (l : Fin g → ℂ))).base).obj (P.L.U i) := by
    rw [hpt]
    exact hi
  have hA := hθ i w hi
  have hB := hθ i (w + (l : Fin g → ℂ)) hi'
  rw [hpt] at hB
  have hE := hB.symm.trans hA
  have hF := a.u.fr_ne (fun _ => i) (w + (l : Fin g → ℂ)) (hz _ hi')
  have hw : a.u.fr (fun _ => i) w =
      (a.χ l * Complex.exp (Real.pi * a.herm w l + Real.pi / 2 * a.herm l l)) *
        a.u.fr (fun _ => i) (w + (l : Fin g → ℂ)) := hfr l (fun _ => i) w (hz w hi)
  rw [hw, mul_pow] at hE
  apply mul_right_cancel₀ (pow_ne_zero n hF)
  rw [hE]
  ring

end GlobalTheory.CompanionTheory.Ar.Sl.Fac
end
end

section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.FlagConst

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

theorem exists_C_eq_of_isAlgebraic {k I : Type} [Field k] (P : MvPolynomial I k) (h : IsAlgebraic k P) :
    ∃ p : k, MvPolynomial.C p = P := by
  by_cases h0 : P = 0
  · exact ⟨0, by simp [h0]⟩
  obtain ⟨r, hr, hd⟩ := h.exists_nonzero_dvd (mem_nonZeroDivisors_of_ne_zero h0)
  have hu : IsUnit P := isUnit_of_dvd_unit hd ((IsUnit.mk0 r hr).map (algebraMap k _))
  obtain ⟨p, -, hp⟩ := MvPolynomial.isUnit_iff_eq_C_of_isReduced.1 hu
  exact ⟨p, hp.symm⟩

theorem mem_range_of_isAlgebraic {k L I : Type} [Field k] [Field L] [Algebra k L] (x : I → L)
    (hx : AlgebraicIndependent k x) (ht : IntermediateField.adjoin k (Set.range x) = ⊤) (a : L)
    (ha : IsAlgebraic k a) : a ∈ (algebraMap k L).range := by
  let g : MvPolynomial I k →ₐ[k] L := MvPolynomial.aeval x
  have hg : Function.Injective g := hx
  letI : Algebra (MvPolynomial I k) L := g.toRingHom.toAlgebra
  have hmap : ∀ P : MvPolynomial I k, algebraMap (MvPolynomial I k) L P = g P := fun _ => rfl
  haveI : IsScalarTower k (MvPolynomial I k) L := IsScalarTower.of_algebraMap_eq fun r => (g.commutes r).symm
  haveI : FaithfulSMul (MvPolynomial I k) L := (faithfulSMul_iff_algebraMap_injective _ _).2 hg
  haveI : IsFractionRing (MvPolynomial I k) L := by
    refine IsFractionRing.of_field _ _ fun z => ?_
    have hz : z ∈ IntermediateField.adjoin k (Set.range x) := ht ▸ IntermediateField.mem_top
    obtain ⟨r, s, e⟩ := (IntermediateField.mem_adjoin_range_iff k x z).1 hz
    exact ⟨r, s, e⟩
  have hi : IsIntegral (MvPolynomial I k) a := (ha.isIntegral).tower_top
  obtain ⟨P, hP⟩ := IsIntegrallyClosed.isIntegral_iff.1 hi
  have hPa : IsAlgebraic k P := by
    rw [← isAlgebraic_algHom_iff g hg, ← hmap, hP]
    exact ha
  obtain ⟨p, rfl⟩ := exists_C_eq_of_isAlgebraic P hPa
  refine ⟨p, ?_⟩
  rw [← hP, hmap]
  exact (g.commutes p).symm

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l}

theorem exists_cst₀ {Y : Model Xo c (algebraMap (𝓞 c.F) c.F)} {S : Finset ℕ} {Ω : Type} [Field Ω] {K : Type} [Fintype K]
    {J : K → Type} {y : (Σ k, J k) → Ω} (𝔐 : HodgeCpt Y S y) :
    ∃ cst₀ : c.F →+* 𝔐.Ω₀, 𝔐.fn.comp cst₀ = 𝔐.cst ∧
      𝔐.ξ₀ ≫ Y.s = spMap (cst₀.comp (algebraMap (𝓞 c.F) c.F)) := by
  haveI : FiniteDimensional ℚ c.F := c.fin
  haveI : NumberField c.F := {}
  let b₀ : 𝓞 c.F →+* 𝔐.Ω₀ := (Spec.preimage (𝔐.ξ₀ ≫ Y.s)).hom
  have hb : 𝔐.ξ₀ ≫ Y.s = spMap b₀ := (Spec.map_preimage _).symm
  have hc : 𝔐.fn.comp b₀ = 𝔐.cst.comp (algebraMap (𝓞 c.F) c.F) := by
    have hsp : spMap (𝔐.fn.comp b₀) = spMap (𝔐.cst.comp (algebraMap (𝓞 c.F) c.F)) := by
      have hd : 𝔐.ξ ≫ 𝔐.f = spMap 𝔐.fn ≫ 𝔐.ξ₀ := 𝔐.fn_over
      have hm : spMap (𝔐.fn.comp b₀) = spMap 𝔐.fn ≫ spMap b₀ := by
        rw [← Spec.map_comp]; rfl
      rw [hm, ← hb, ← 𝔐.cst_over, ← Category.assoc, ← Category.assoc, hd]
    have := CommRingCat.hom_ext_iff.1 (Spec.map_injective hsp)
    simpa using this
  have hinj : Function.Injective b₀ := by
    intro u v huv
    have h := congrArg 𝔐.fn huv
    have hu : ∀ w, 𝔐.fn (b₀ w) = 𝔐.cst (algebraMap (𝓞 c.F) c.F w) := fun w => RingHom.congr_fun hc w
    rw [hu, hu] at h
    exact IsFractionRing.injective (𝓞 c.F) c.F (𝔐.cst.injective h)
  let cst₀ : c.F →+* 𝔐.Ω₀ := IsFractionRing.lift hinj
  have hl : cst₀.comp (algebraMap (𝓞 c.F) c.F) = b₀ := by
    ext w
    exact IsFractionRing.lift_algebraMap hinj w
  refine ⟨cst₀, ?_, by rw [hl, hb]⟩
  refine IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 c.F)) ?_
  rw [RingHom.comp_assoc, hl, hc]

theorem isAlgebraic_mem_cst_range : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (Fl : 𝔐.Flag), SplitComps Y → Fl.deg = 1 → ∀ a : Ω, IsAlgebraic ℤ a → a ∈ 𝔐.cst.range := by
  intro E _ _ _ H D l Xo c Y S Ω _ K _ J y 𝔐 Fl hS hdeg a ha
  obtain ⟨cst₀, h1, h2⟩ := exists_cst₀ 𝔐
  haveI : CharZero Ω := charZero_of_injective_ringHom 𝔐.cst.injective
  letI : Algebra 𝔐.Ω₀ Ω := 𝔐.fn.toAlgebra
  obtain ⟨-, u, -, -, -, -, hdiag, hup, -, hind, -, hfin⟩ := Fl.generic
  rw [hdeg] at hfin
  let x : (Σ q : CMType H ⊕ CMType H, {lk : Fin (labelRk D q) × Fin (labelRk D q) // lk.2 < lk.1}) → Ω :=
    fun q => u q.1 q.2.1.1 q.2.1.2
  let A := IntermediateField.adjoin 𝔐.Ω₀
    (Set.range fun q : Σ σ, Fin (labelRk D σ) × Fin (labelRk D σ) => u q.1 q.2.1 q.2.2)
  have hA : A = ⊤ := by
    have hb := Subalgebra.bot_eq_top_of_finrank_eq_one hfin
    refine eq_top_iff.2 fun z _ => ?_
    have hz : z ∈ (⊥ : Subalgebra A Ω) := hb ▸ Algebra.mem_top
    obtain ⟨w, rfl⟩ := Algebra.mem_bot.1 hz
    exact w.2
  have ht : IntermediateField.adjoin 𝔐.Ω₀ (Set.range x) = ⊤ := by
    refine eq_top_iff.2 (hA ▸ ?_)
    refine IntermediateField.adjoin_le_iff.2 ?_
    rintro _ ⟨⟨σ, l', k⟩, rfl⟩
    rcases lt_trichotomy l' k with h | h | h
    · show u σ l' k ∈ _
      rw [hup σ l' k h]
      exact zero_mem _
    · subst h
      show u σ l' l' ∈ _
      rw [hdiag σ l']
      exact one_mem _
    · exact IntermediateField.subset_adjoin _ _ ⟨⟨σ, ⟨(l', k), h⟩⟩, rfl⟩
  have hal : IsAlgebraic 𝔐.Ω₀ a := by
    haveI : CharZero 𝔐.Ω₀ := charZero_of_injective_ringHom cst₀.injective
    exact ha.extendScalars (RingHom.injective_int _)
  obtain ⟨a₀, rfl⟩ := mem_range_of_isAlgebraic x hind ht a hal
  have ha₀ : IsAlgebraic ℤ a₀ :=
    (isAlgebraic_algHom_iff (IsScalarTower.toAlgHom ℤ 𝔐.Ω₀ Ω) (algebraMap 𝔐.Ω₀ Ω).injective).1 ha
  obtain ⟨k, rfl⟩ := hS 𝔐.Ω₀ 𝔐.ξ₀ cst₀ 𝔐.gen₀ h2 a₀ ha₀
  exact ⟨k, (RingHom.congr_fun h1 k).symm⟩

end GlobalTheory.CompanionTheory.Ar.FlagConst
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl
open GlobalTheory

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Sl.FrameFn

variable {X Y : Scheme.{0}}

theorem valF_eq_valAt' (x : Sp ℂ ⟶ X) (U : X.Opens) (f : Γ(X, U)) : valF x U f = valAt' x U f := by
  by_cases h : ⊤ ≤ x ⁻¹ᵁ U
  · rw [valF, dite_eq_left h, valAt', dite_eq_left h, valAt]
  · rw [valF, dite_eq_right h, valAt', dite_eq_right h]

theorem top_le_wchart {K : Type} [Fintype K] (L : LB X) (φ : Y ⟶ X) (x : Sp ℂ ⟶ Y) (i : L.ι)
    (h : ⊤ ≤ (x ≫ φ) ⁻¹ᵁ L.U i) : ⊤ ≤ x ⁻¹ᵁ LB.wchart L (fun _ : K => φ) (fun _ => i) :=
  fun p hp => Set.mem_iInter.2 fun _ => by
    have := h hp
    simpa using this

theorem valAt'_g_const {K : Type} [Fintype K] [Unique K] (L : LB X) (φ : Y ⟶ X) (e : ℤ) (x : Sp ℂ ⟶ Y) (i i' : L.ι)
    (h : ⊤ ≤ x ⁻¹ᵁ (LB.wchart L (fun _ : K => φ) (fun _ => i) ⊓ LB.wchart L (fun _ : K => φ) (fun _ => i'))) :
    valAt' x _ ((LB.LinComb L (K := K) (fun _ => φ) (fun _ => e)).g (fun _ => i) (fun _ => i')).val =
      valAt' (x ≫ φ) (L.U i ⊓ L.U i') (L.g i i').val ^ e := by
  have hle : LB.wchart L (fun _ : K => φ) (fun _ => i) ⊓ LB.wchart L (fun _ : K => φ) (fun _ => i') ≤
      φ ⁻¹ᵁ (L.U i ⊓ L.U i') :=
    le_inf (inf_le_left.trans (LB.wchart_le L _ _ default)) (inf_le_right.trans (LB.wchart_le L _ _ default))
  have key : ((LB.LinComb L (K := K) (fun _ => φ) (fun _ => e)).g (fun _ => i) (fun _ => i') :
      Γ(Y, LB.wchart L (fun _ : K => φ) (fun _ => i) ⊓ LB.wchart L (fun _ : K => φ) (fun _ => i'))ˣ) =
      (res hle (pullU φ _ (L.g i i'))) ^ e :=
    Fintype.prod_unique (M := Γ(Y, LB.wchart L (fun _ : K => φ) (fun _ => i) ⊓ LB.wchart L (fun _ : K => φ) (fun _ => i'))ˣ) _
  refine (congrArg (fun u : Γ(Y, LB.wchart L (fun _ : K => φ) (fun _ => i) ⊓
    LB.wchart L (fun _ : K => φ) (fun _ => i'))ˣ => valAt' x _ u.val) key).trans ?_
  refine (valAt'_units_zpow x h _ e).trans ?_
  congr 1
  exact (valAt'_map x _ _ h).trans (valAt'_comp x φ _ _)

end GlobalTheory.CompanionTheory.Ar.Sl.FrameFn

namespace GlobalTheory.CompanionTheory.Ar.Sl.FrameFn
variable {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] {P : RigLB G} {z : Sp ℂ ⟶ S} {g : ℕ}

theorem exists_chart_pt (a : ArchFrame P z g) (w : Fin g → ℂ) : ∃ i, ⊤ ≤ a.pt w ⁻¹ᵁ P.L.U i := by
  have h : a.pt w (default : PrimeSpectrum ℂ) ∈ (⨆ i, P.L.U i : G.left.Opens) := by
    rw [P.isLB.cover]; trivial
  obtain ⟨i, hi⟩ := (TopologicalSpace.Opens.mem_iSup).1 h
  exact ⟨i, (top_le_preimage_iff_mem _ _).2 hi⟩

theorem top_le_frame (a : ArchFrame P z g) (w : Fin g → ℂ) (i : P.L.ι) (h : ⊤ ≤ a.pt w ⁻¹ᵁ P.L.U i) :
    ⊤ ≤ (a.u.ex w).left ⁻¹ᵁ (P.L.pull a.φ).U (fun _ => i) :=
  top_le_wchart (K := PUnit) P.L a.φ (a.u.ex w).left i h

theorem top_le_sec (a : ArchFrame P z g) (n : ℕ) (w : Fin g → ℂ) (i : P.L.ι) (h : ⊤ ≤ a.pt w ⁻¹ᵁ P.L.U i) :
    ⊤ ≤ a.pt w ⁻¹ᵁ (LB.LinComb P.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => (n : ℤ))).U (fun _ => i) :=
  top_le_wchart (K := Fin 1) P.L (𝟙 G.left) (a.pt w) i (by simpa using h)

theorem fr_change (a : ArchFrame P z g) (w : Fin g → ℂ) (i j : P.L.ι) (hi : ⊤ ≤ a.pt w ⁻¹ᵁ P.L.U i)
    (hj : ⊤ ≤ a.pt w ⁻¹ᵁ P.L.U j) :
    a.u.fr (fun _ => i) w = valAt' (a.pt w) (P.L.U i ⊓ P.L.U j) (P.L.g i j).val * a.u.fr (fun _ => j) w := by
  have h : ⊤ ≤ (a.u.ex w).left ⁻¹ᵁ ((P.L.pull a.φ).U (fun _ => i) ⊓ (P.L.pull a.φ).U (fun _ => j)) :=
    (top_le_preimage_inf _ _ _).2 ⟨top_le_frame a w i hi, top_le_frame a w j hj⟩
  refine (a.u.fr_compat _ _ w h).trans ?_
  have := valAt'_g_const (K := PUnit) P.L a.φ 1 (a.u.ex w).left i j h
  rw [zpow_one] at this
  exact congrArg (· * a.u.fr (fun _ => j) w) this

theorem sec_change (a : ArchFrame P z g) {n : ℕ} (s : Out.H0 P.L n) (w : Fin g → ℂ) (i j : P.L.ι)
    (hi : ⊤ ≤ a.pt w ⁻¹ᵁ P.L.U i) (hj : ⊤ ≤ a.pt w ⁻¹ᵁ P.L.U j) :
    valF (a.pt w) _ (s.f fun _ => i) =
      valAt' (a.pt w) (P.L.U i ⊓ P.L.U j) (P.L.g i j).val ^ n * valF (a.pt w) _ (s.f fun _ => j) := by
  have h : ⊤ ≤ a.pt w ⁻¹ᵁ ((LB.LinComb P.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => (n : ℤ))).U (fun _ => i) ⊓
      (LB.LinComb P.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => (n : ℤ))).U (fun _ => j)) :=
    (top_le_preimage_inf _ _ _).2 ⟨top_le_sec a n w i hi, top_le_sec a n w j hj⟩
  have e := congrArg (valAt' (a.pt w) _) (s.compat (fun _ => i) (fun _ => j))
  rw [valAt'_mul, valAt'_map _ _ _ h, valAt'_map _ _ _ h] at e
  have t := valAt'_g_const (K := Fin 1) P.L (𝟙 G.left) (n : ℤ) (a.pt w) i j h
  rw [Category.comp_id, zpow_natCast] at t
  rw [valF_eq_valAt', valF_eq_valAt', e, t]

theorem unique_fn (a : ArchFrame P z g) (n : ℕ) (s : Out.H0 P.L n) : ∃! θ, a.IsFn s θ := by
  choose c hc using exists_chart_pt a
  have hne : ∀ w i, ⊤ ≤ a.pt w ⁻¹ᵁ P.L.U i → a.u.fr (fun _ => i) w ≠ 0 :=
    fun w i h => a.u.fr_ne _ w (top_le_frame a w i h)
  refine ⟨fun w => valF (a.pt w) _ (s.f fun _ => c w) / a.u.fr (fun _ => c w) w ^ n, ?_, ?_⟩
  · intro i w hi
    have h1 := fr_change a w i (c w) hi (hc w)
    have h2 := sec_change a s w i (c w) hi (hc w)
    have n1 := hne w (c w) (hc w)
    show _ = _ / _ * _
    rw [h2, h1, mul_pow]
    field_simp
  · intro θ hθ
    funext w
    have := hθ (c w) w (hc w)
    rw [this, mul_div_assoc, div_self (pow_ne_zero _ (hne w _ (hc w))), _root_.mul_one]

end GlobalTheory.CompanionTheory.Ar.Sl.FrameFn

theorem GlobalTheory.CompanionTheory.Ar.Sl.frame_fn_existsUnique : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (P : RigLB G) (z : Sp ℂ ⟶ S) (g : ℕ) (a : ArchFrame P z g) (n : ℕ) (s : Out.H0 P.L n), ∃! θ, a.IsFn s θ :=
  by
  intro S G _ _ P z g a n s
  exact GlobalTheory.CompanionTheory.Ar.Sl.FrameFn.unique_fn a n s
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl

namespace GlobalTheory.CompanionTheory.Ar.Sl

theorem isFn_differentiable : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (P : RigLB G) (z : Sp ℂ ⟶ S) (g : ℕ) (a : ArchFrame P z g) (n : ℕ) (s : Out.H0 P.L n) (θ : (Fin g → ℂ) → ℂ), a.IsFn s θ → Differentiable ℂ θ := by
  intro S G _ _ P z g a n s θ hθ w₀
  have hm : a.pt w₀ (default : PrimeSpectrum ℂ) ∈ ⨆ i, P.L.U i := by
    rw [P.isLB.cover]; trivial
  obtain ⟨i, hi'⟩ := TopologicalSpace.Opens.mem_iSup.1 hm
  have hi : ⊤ ≤ a.pt w₀ ⁻¹ᵁ P.L.U i := (GlobalTheory.top_le_preimage_iff_mem _ _).2 hi'
  let W : G.left.Opens := LB.wchart P.L (fun _ : Fin 1 => 𝟙 G.left) (fun _ => i)
  let Q : a.A.left.Opens := (P.L.pull a.φ).U (fun _ => i)
  let C : Set (Fin g → ℂ) := {w | ⊤ ≤ (a.u.ex w).left ⁻¹ᵁ Q}
  have hCpt : ∀ w, w ∈ C → ⊤ ≤ a.pt w ⁻¹ᵁ P.L.U i := fun w h y hy =>
    Set.mem_iInter.1 (h hy) PUnit.unit
  have hptC : ∀ w, ⊤ ≤ a.pt w ⁻¹ᵁ P.L.U i → w ∈ C := fun w h y hy =>
    Set.mem_iInter.2 fun _ => h hy
  have hCV : ∀ w, w ∈ C → ⊤ ≤ (a.u.ex w).left ⁻¹ᵁ (a.φ ⁻¹ᵁ W) := fun w h y hy =>
    Set.mem_iInter.2 fun _ => hCpt w h hy
  have ho : IsOpen C := (a.u.hol Q 0).1
  have hv : DifferentiableOn ℂ (fun w => valAt' (a.u.ex w).left (a.φ ⁻¹ᵁ W) ((a.φ.app W).hom (s.f fun _ => i))) C :=
    (a.u.hol _ _).2.mono hCV
  have hfr : DifferentiableOn ℂ (fun w => a.u.fr (fun _ => i) w ^ n) C := (a.u.fr_hol _).pow n
  have hne : ∀ w ∈ C, a.u.fr (fun _ => i) w ^ n ≠ 0 := fun w hw => pow_ne_zero n (a.u.fr_ne _ w hw)
  have hq : DifferentiableOn ℂ θ C := by
    refine (hv.mul (hfr.inv hne)).congr fun w hw => ?_
    have e := hθ i w (hCpt w hw)
    have e' : valF (a.pt w) W (s.f fun _ => i) = valAt' (a.pt w) W (s.f fun _ => i) := rfl
    have e4 : valAt' (a.u.ex w).left (a.φ ⁻¹ᵁ W) ((a.φ.app W).hom (s.f fun _ => i)) = θ w * a.u.fr (fun _ => i) w ^ n :=
      (GlobalTheory.valAt'_comp (a.u.ex w).left a.φ W (s.f fun _ => i)).trans (e'.symm.trans e)
    exact (mul_inv_cancel_right₀ (hne w hw) (θ w)).symm.trans (congrArg (· * (a.u.fr (fun _ => i) w ^ n)⁻¹) e4.symm)
  exact (hq.differentiableAt (ho.mem_nhds (hptC w₀ hi)))

end GlobalTheory.CompanionTheory.Ar.Sl
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.T.hodge_comp_comparison_middle : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S₀ S : Finset ℕ) (Ω₁ Ω : Type) [Field Ω₁] [Field Ω] (K₁ : Type) [Fintype K₁] (J₁ : K₁ → Type) [∀ k, Fintype (J₁ k)] (y₁ : (Σ k, J₁ k) → Ω₁) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (A : HodgeCpt Y S₀ y₁) (Fl : A.Flag) (B : HodgeCpt Y S y) (i : Ω₁ →+* Ω) (h : B.X ⟶ A.X) (jA : A.Li →+ B.Li), (letI := i.toAlgebra; FiniteDimensional Ω₁ Ω) → GlobalTheory.CompanionTheory.Ar.Dominates B.ξ A.ξ h i → B.f = h ≫ A.f → B.cst = i.comp A.cst → IsExtOver i jA → (∀ e, (B.M.pt (jA e)).left ≫ B.m.φ = spMap (dualMap i) ≫ (A.M.pt e).left ≫ A.m.φ) → (∀ a e, jA (A.ρ a e) = B.ρ a (jA e)) → ∃ (Li₀ : Type) (_ : AddCommGroup Li₀) (_ : Module B.Ω₀ Li₀) (M₀ : LieModel Y.t.G B.ξ₀ Li₀) (j : Li₀ →+ B.Li) (V₀ : CMType H ⊕ CMType H → Submodule B.Ω₀ Li₀), (∀ s, Submodule.span Ω (Set.range fun a => jA (Fl.b s a)) = B.Vgen s) ∧ (∀ e, (B.M.pt (j e)).left ≫ B.m.φ = spMap (dualMap B.fn) ≫ (M₀.pt e).left) ∧ (∀ s e, e ∈ V₀ s ↔ j e ∈ B.Vgen s) ∧ (letI := B.fn.toAlgebra; IsGenericFlag (Ω' := Ω) j V₀ (fun s a => jA (Fl.b s a)) ((letI := i.toAlgebra; Module.finrank Ω₁ Ω) * Fl.deg)) := by
  exact @GlobalTheory.CompanionTheory.Ar.FlagRead.generic_read
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.T.predual_vector_bundle : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (Li : Type) [AddCommGroup Li] [Module Ω Li] (L : Lat ξ (Module.Dual Ω Li)) (T : Set (Cpt ξ)) (r : ℕ) (V : Submodule Ω Li) [FiniteDimensional Ω V], (L.map V.dualRestrict).IsVBOn T r ⊤ → (L.predualIn V).IsVBOn T r V := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Lat.predualIn_isVBOn | exact GlobalTheory.CompanionTheory.Ar.Lat.predualIn_isVBOn | (intros; apply GlobalTheory.CompanionTheory.Ar.Lat.predualIn_isVBOn <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.T.twisted_hodge_cpt_flag : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O O' : Type) [CommRing O] [CommRing O'] (β : O →+* c.F) (β' : O' →+* c.F) (Y : Model Xo c β) (Y' : Model Xo c β') (g : HostAut H) (Φ : Xo.X ≅ Xo.X) (n : SABMap (twistSAB Xo.univ.t g) Xo.univ.t Φ.hom) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) (y : (Σ k, J k) → Ω) (A : HodgeCpt Y S y) (A' : HodgeCpt Y' S y) (Fl : A.Flag) (Fl' : A'.Flag) (ψ : A'.Ω₀ ≃+* A.Ω₀) (θ : Fl.Li₀ ≃+ Fl'.Li₀) (φ : A.Li ≃ₗ[Ω] A'.Li), Mono (spMap β) → Mono (spMap β') → A.fn.comp ψ.toRingHom = A'.fn → (∀ w, TwTan n Y Y' ((A.M.pt w).left ≫ A.m.φ) ((A'.M.pt (φ w)).left ≫ A'.m.φ)) → (∀ e, TwTan n Y Y' (Fl.M₀.pt e).left (spMap (dualMap ψ.toRingHom) ≫ (Fl'.M₀.pt (θ e)).left)) → (∀ e, φ (Fl.j e) = Fl'.j (θ e)) ∧ ∀ s s' (r : ℕ) (b : Fin r → Fl.Li₀) (u : Matrix (Fin r) (Fin r) Ω), (∀ k, flagStep Ω (Fl.b s) k = flagStep Ω (fun a => ∑ q, u q a • Fl.j (b q)) k) → (∀ k, flagStep Ω (Fl'.b s') k = flagStep Ω (fun a => ∑ q, u q a • Fl'.j (θ (b q))) k) → ∀ k, (flagStep Ω (Fl.b s) k).map φ.toLinearMap = flagStep Ω (Fl'.b s') k := by
  first | exact @GlobalTheory.CompanionTheory.Ar.FlagMatch.matched_generic_flags_carried | exact GlobalTheory.CompanionTheory.Ar.FlagMatch.matched_generic_flags_carried | (intros; apply GlobalTheory.CompanionTheory.Ar.FlagMatch.matched_generic_flags_carried <;> assumption)
end

section

open NumberField TensorProduct Matrix GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp

theorem _root_.GlobalTheory.T.adapted_gram_det_positive : ∀ (E L Ψ : Type) [Field E] [NumberField E] [Field L] [NumberField L] (V : Type) [AddCommGroup V] [Module L V] [Module (𝓞 L) V] [IsScalarTower (𝓞 L) L V] (A : LinPt E L Ψ V) (s : Ψ ⊕ Ψ) (r k : ℕ) (v : Fin r → V) (q : Fin k → A.Λ), IsOFamily A.ρ A.I v → A.IsAdapted s v q → (∀ i, (q i : V) ∈ A.eig s) → ∀ e : L →+* ℂ, 0 < A.gramDet e q := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.gramDet_pos_of_adapted | exact GlobalTheory.CompanionTheory.Ar.Cusp.gramDet_pos_of_adapted | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.gramDet_pos_of_adapted <;> assumption)
end
