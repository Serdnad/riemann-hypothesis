module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle026
public import Mathlib.RingTheory.Flat.Basic
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle101
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle016
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle122
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle132
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle130
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle128
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle127
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.MapHComp
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.MemBoundariesZeroIff
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.HarishChandraFormulaStatement
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.Bundle001
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.SEqOne
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.CoassocSimps
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.OneFormMapEqKaehlerDifferentialMap
import Development.AbelianVarietyTheory.Definitions.Divisors.Pullback1MemHodgeFiltration
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.HodgeWedgeFields.H1CommutesBaseChange
public import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsDPMorphismBot

@[expose] public section

section

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.Axis
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompanionTheory.Axis

theorem rTensor_coords_bijective {R : Type} [CommRing R] {I : Type} [Finite I] {P : Type}
    [AddCommGroup P] [Module R P] (M : I → Type) [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
    (e : P ≃ₗ[R] ∀ i, M i) (N : Type) [AddCommGroup N] [Module R N] :
    Function.Bijective (LinearMap.pi fun i =>
      ((LinearMap.proj i : (∀ i, M i) →ₗ[R] M i) ∘ₗ e.toLinearMap).rTensor N) := by
  classical
  cases nonempty_fintype I
  have hcomp : (LinearMap.pi fun i =>
      ((LinearMap.proj i : (∀ i, M i) →ₗ[R] M i) ∘ₗ e.toLinearMap).rTensor N) =
      (TensorProduct.piLeft (R := R) (N := N) (M := M)).toLinearMap ∘ₗ
        (LinearEquiv.rTensor N e).toLinearMap := by
    apply TensorProduct.ext'
    intro p n
    funext i
    simp
  rw [hcomp]
  exact ((LinearEquiv.rTensor N e).trans
    (TensorProduct.piLeft (R := R) (N := N) (M := M))).bijective

section Cochains

variable {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R)

def oneCochainsPiArrowsEquiv : C1 F ≃ₗ[R] ∀ a : (Σ T : C, Σ T' : C, (T ⟶ T')), F.obj a.2.1 where
  toFun f a := f a.1 a.2.1 a.2.2
  invFun g T T' φ := g ⟨T, T', φ⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

def twoCochainsPiComposableEquiv : C2 F ≃ₗ[R]
    ∀ a : (Σ T : C, Σ T' : C, Σ T'' : C, (T ⟶ T') × (T' ⟶ T'')), F.obj a.2.2.1 where
  toFun f a := f a.1 a.2.1 a.2.2.1 a.2.2.2.1 a.2.2.2.2
  invFun g T T' T'' φ ψ := g ⟨T, T', T'', φ, ψ⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

def evC {T T' : C} (φ : T ⟶ T') : C1 F →ₗ[R] F.obj T' where
  toFun f := f T T' φ
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem evaluation_comp_coboundary_one {T T' T'' : C} (φ : T ⟶ T') (ψ : T' ⟶ T'') :
    (LinearMap.proj (⟨T, T', T'', φ, ψ⟩ : Σ T : C, Σ T' : C, Σ T'' : C, (T ⟶ T') × (T' ⟶ T'')) :
        (∀ a : (Σ T : C, Σ T' : C, Σ T'' : C, (T ⟶ T') × (T' ⟶ T'')), F.obj a.2.2.1) →ₗ[R] _) ∘ₗ
      (twoCochainsPiComposableEquiv F).toLinearMap ∘ₗ d1 F =
    (mp F ψ).toLinearMap ∘ₗ evC F φ - evC F (φ ≫ ψ) + evC F ψ := by
  ext f
  rfl

end Cochains

theorem cocycle_of_flat (R : Type) [CommRing R] (C : Type) [Category.{0} C] [Finite C]
    [Quiver.IsThin C] (F : C ⥤ CommAlgCat.{0} R)
    (N : Type) [AddCommGroup N] [Module R N] [Module.Flat R N]
    (f : ∀ (T T' : C) (_ : T ⟶ T'), F.obj T' ⊗[R] N)
    (hf : ∀ (T T' T'' : C) (φ : T ⟶ T') (ψ : T' ⟶ T''),
      f T T'' (φ ≫ ψ) = (mp F ψ).toLinearMap.rTensor N (f T T' φ) + f T' T'' ψ) :
    ∃ t : Z1 F ⊗[R] N, ∀ (T T' : C) (φ : T ⟶ T'), (evZ F φ).rTensor N t = f T T' φ := by
  haveI : ∀ T T' : C, Finite (T ⟶ T') := fun _ _ => Finite.of_subsingleton
  have b1 := rTensor_coords_bijective (R := R) _ (oneCochainsPiArrowsEquiv F) N
  have b2 := rTensor_coords_bijective (R := R) _ (twoCochainsPiComposableEquiv F) N
  obtain ⟨v, hv⟩ := b1.2 (fun a => f a.1 a.2.1 a.2.2)
  have hv' : ∀ (T T' : C) (φ : T ⟶ T'), (evC F φ).rTensor N v = f T T' φ := fun T T' φ =>
    congrFun hv ⟨T, T', φ⟩
  have hw : (d1 F).rTensor N v = 0 := by
    apply b2.1
    rw [map_zero]
    funext ⟨T, T', T'', φ, ψ⟩
    have h := congrArg (fun g => LinearMap.rTensor N g v) (evaluation_comp_coboundary_one F φ ψ)
    simp only [LinearMap.rTensor_add, LinearMap.rTensor_sub, LinearMap.rTensor_comp,
      LinearMap.add_apply, LinearMap.sub_apply, LinearMap.comp_apply, hv'] at h
    rw [hf T T' T'' φ ψ] at h
    simp only [LinearMap.pi_apply, Pi.zero_apply, LinearMap.rTensor_comp, LinearMap.comp_apply]
    rw [h]
    abel
  have hex : Function.Exact (Z1 F).subtype (d1 F) := fun x => by
    rw [← LinearMap.mem_ker, ← commAlgFunctorCocyclesOne_eq_ker]
    simp
  obtain ⟨t, ht⟩ := (Module.Flat.rTensor_exact N hex v).1 hw
  refine ⟨t, fun T T' φ => ?_⟩
  have : evZ F φ = evC F φ ∘ₗ (Z1 F).subtype := rfl
  rw [this, LinearMap.rTensor_comp, LinearMap.comp_apply, ht, hv']

end GlobalTheory.CompanionTheory.Axis
end
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter GlobalTheory.CompanionTheory.Equi
open scoped Classical

noncomputable section

namespace GlobalTheory.CompanionTheory.Equi.LatSum

section Abstract

variable {A O Q ι : Type} [AddCommGroup A] [AddCommGroup O] [Fintype ι] [Fintype Q]

def reps (j : O →+ A) (rep : Q → O) : Finset (ι → A) :=
  Finset.univ.image fun (c : ι → Q) (i : ι) => j (rep (c i))

theorem card_reps (j : O →+ A) (hj : Function.Injective j) (q : O → Q) (rep : Q → O)
    (hrep : ∀ c, q (rep c) = c) :
    (reps (ι := ι) j rep).card = Fintype.card Q ^ Fintype.card ι := by
  unfold reps
  rw [Finset.card_image_of_injective, Finset.card_univ, Fintype.card_fun]
  intro c c' h
  funext i
  have h1 : j (rep (c i)) = j (rep (c' i)) := congrFun h i
  have h2 := congrArg q (hj h1)
  rwa [hrep, hrep] at h2

theorem tile_pi (H : AddSubgroup O) (j : O →+ A) (hj : Function.Injective j) (q : O → Q) (rep : Q → O)
    (hrep : ∀ c, q (rep c) = c) (hq : ∀ a b, q a = q b ↔ a - b ∈ H) (D₀ : Set A)
    (hD : ∀ y : A, ∃! a : O, y - j a ∈ D₀) (y : ι → A) :
    ∃! p : (ι → A) × (ι → A), p.1 ∈ reps (ι := ι) j rep ∧
      p.2 ∈ AddSubgroup.pi Set.univ (fun _ : ι => H.map j) ∧
      y - p.1 - p.2 ∈ Set.pi Set.univ (fun _ : ι => D₀) := by
  choose a ha hau using fun i => hD (y i)
  refine ⟨(fun i => j (rep (q (a i))), fun i => j (a i - rep (q (a i)))), ⟨?_, ?_, ?_⟩, ?_⟩
  · exact Finset.mem_image.2 ⟨fun i => q (a i), Finset.mem_univ _, rfl⟩
  · intro i _
    refine AddSubgroup.mem_map.2 ⟨a i - rep (q (a i)), ?_, rfl⟩
    exact (hq _ _).1 (hrep _).symm
  · intro i _
    have : y i - j (rep (q (a i))) - j (a i - rep (q (a i))) = y i - j (a i) := by
      rw [map_sub]; abel
    simpa [this] using ha i
  · rintro ⟨p₁, p₂⟩ ⟨h1, h2, h3⟩
    obtain ⟨c, -, rfl⟩ := Finset.mem_image.1 h1
    have hl : ∀ i, ∃ l ∈ H, j l = p₂ i := fun i => by
      obtain ⟨l, hl, e⟩ := AddSubgroup.mem_map.1 (h2 i (Set.mem_univ i))
      exact ⟨l, hl, e⟩
    choose l hlH hlj using hl
    have hai : ∀ i, rep (c i) + l i = a i := fun i => by
      refine hau i _ ?_
      have h4 := h3 i (Set.mem_univ i)
      have h5 : y i - j (rep (c i) + l i) = (y - (fun i => j (rep (c i))) - p₂) i := by
        simp only [Pi.sub_apply, map_add (f := _), hlj]; abel
      show y i - j (rep (c i) + l i) ∈ D₀
      rw [h5]; exact h4
    have hc : ∀ i, q (a i) = c i := fun i => by
      have h6 : q (a i) = q (rep (c i)) := (hq _ _).2 (by rw [← hai i]; simpa using hlH i)
      rwa [hrep] at h6
    refine Prod.ext (funext fun i => ?_) (funext fun i => ?_)
    · show j (rep (c i)) = j (rep (q (a i)))
      rw [hc]
    · show p₂ i = j (a i - rep (q (a i)))
      rw [hc, ← hai i, add_sub_cancel_left, hlj]

end Abstract

def scal {R : Type} (ι : Type) [CommRing R] (t : R) : (ι → R) →+ (ι → R) where
  toFun y i := t * y i
  map_zero' := by funext i; simp
  map_add' x y := by funext i; simp [mul_add]

end GlobalTheory.CompanionTheory.Equi.LatSum


open GlobalTheory.CompanionTheory.Equi.LatSum in
theorem GlobalTheory.CompanionTheory.Equi.lat_sum : ∀ (F : Type) [Field F] [NumberField F], IsTotallyReal F → ∀ θ : ℝ →+* Ainf F, Continuous θ → ∀ li : Measure (Ainf F), IsStdInf li → ∀ (ι : Type) [Fintype ι] (I : Ideal (𝓞 F)), I ≠ ⊥ → ∀ (x0 : ι → F) (φ : (ι → Ainf F) → ℝ), Continuous φ → HasCompactSupport φ → (∀ ε : ℝ, 0 < ε → Summable fun x : latCoset I x0 => φ (fun i => θ ε * algebraMap F (Ainf F) (x.1 i))) ∧ Tendsto (fun ε : ℝ => ε ^ (Module.finrank ℚ F * Fintype.card ι) * ∑' x : latCoset I x0, φ (fun i => θ ε * algebraMap F (Ainf F) (x.1 i))) (𝓝[>] 0) (𝓝 (((Ideal.absNorm I : ℝ) ^ Fintype.card ι)⁻¹ * ∫ y, φ y ∂(Measure.pi fun _ => li))) := by
  intro F _ _ hF θ hθ li hli ι _ I hI x0 φ hφ hφs
  haveI : BorelSpace (Ainf F) := ⟨rfl⟩
  obtain ⟨hTR, hLC, hSC, hT2, -⟩ := GlobalTheory.CompanionTheory.SW.isLocR_Ainf F hF
  haveI := hTR
  haveI := hLC
  haveI := hSC
  haveI := hT2
  haveI : li.IsAddHaarMeasure := hli.1
  obtain ⟨D₀, K₀, hDm, hK, hDK, hD1, htile⟩ := GlobalTheory.T.archimedean_fundamental_domain_integers F hF li hli
  have hg : Function.Injective (algebraMap F (Ainf F)) := (algebraMap F (Ainf F)).injective
  let j : 𝓞 F →+ Ainf F := ((algebraMap F (Ainf F)).comp (algebraMap (𝓞 F) F)).toAddMonoidHom
  have hj : Function.Injective j := hg.comp (IsFractionRing.injective (𝓞 F) F)
  let H : AddSubgroup (𝓞 F) := I.toAddSubgroup
  haveI hfin : Finite (𝓞 F ⧸ I) := Ideal.finiteQuotientOfFreeOfNeBot I hI
  letI : Fintype (𝓞 F ⧸ I) := Fintype.ofFinite _
  let rep : 𝓞 F ⧸ I → 𝓞 F := Function.surjInv Ideal.Quotient.mk_surjective
  have hrep : ∀ c, Ideal.Quotient.mk I (rep c) = c := Function.surjInv_eq _
  have hq : ∀ a b, Ideal.Quotient.mk I a = Ideal.Quotient.mk I b ↔ a - b ∈ H := fun a b => Ideal.Quotient.eq
  let Λ : AddSubgroup (ι → Ainf F) := AddSubgroup.pi Set.univ (fun _ : ι => H.map j)
  haveI : Countable (𝓞 F) := (RingOfIntegers.basis F).equivFun.toEquiv.injective.countable
  haveI : Countable (H.map j) := by
    have : (↑(H.map j) : Set (Ainf F)).Countable := (Set.to_countable (H : Set (𝓞 F))).image j
    exact this.to_subtype
  haveI : Countable Λ := by
    refine Function.Injective.countable (f := fun (l : Λ) (i : ι) => (⟨l.1 i, l.2 i (Set.mem_univ i)⟩ : H.map j)) ?_
    intro l l' h
    exact Subtype.ext (funext fun i => congrArg Subtype.val (congrFun h i))
  have hcard : ((reps (ι := ι) j rep).card : ℝ) = (Ideal.absNorm I : ℝ) ^ Fintype.card ι := by
    rw [card_reps j hj (Ideal.Quotient.mk I) rep hrep, Nat.cast_pow, Ideal.absNorm_apply,
      Submodule.cardQuot_apply, Nat.card_eq_fintype_card]
  let T : ℝ → (ι → Ainf F) →+ (ι → Ainf F) := fun ε => scal ι (θ ε)
  have hjoint : Continuous fun p : ℝ × (ι → Ainf F) => T p.1 p.2 :=
    continuous_pi fun i => (hθ.comp continuous_fst).mul ((continuous_apply i).comp continuous_snd)
  have hθ0 : θ 0 = 0 := map_zero θ
  have key := GlobalTheory.T.lattice_point_count_scaling (ι → Ainf F) (Measure.pi fun _ => li) Λ (Set.pi Set.univ fun _ => D₀)
    (Set.pi Set.univ fun _ => K₀) (reps (ι := ι) j rep) T (Module.finrank ℚ F * Fintype.card ι)
    (MeasurableSet.univ_pi fun _ => hDm) (isCompact_univ_pi fun _ => hK)
    (Set.pi_mono fun _ _ => hDK)
    (by rw [Measure.pi_pi]; simp [hD1])
    (fun y => tile_pi H j hj (Ideal.Quotient.mk I) rep hrep hq D₀ htile y)
    (fun ε _ => continuous_pi fun i => continuous_const.mul (continuous_apply i))
    (fun ε hε y => by
      have h1 : θ ε⁻¹ * θ ε = 1 := by rw [← map_mul, inv_mul_cancel₀ hε.ne', map_one]
      have h2 : θ ε * θ ε⁻¹ = 1 := by rw [mul_comm, h1]
      constructor
      · funext i
        show θ ε⁻¹ * (θ ε * y i) = y i
        rw [← mul_assoc, h1, one_mul]
      · funext i
        show θ ε * (θ ε⁻¹ * y i) = y i
        rw [← mul_assoc, h2, one_mul])
    (fun ε hε => GlobalTheory.T.scaling_measure_product_archimedean F hF θ hθ li hli.1 ι ε hε)
    (fun B hB U hU => by
      have h0 : ∀ b ∈ B, ∀ᶠ z : ℝ × (ι → Ainf F) in 𝓝 ((0 : ℝ), b), T z.1 z.2 ∈ U := by
        intro b _
        refine hjoint.continuousAt.eventually_mem ?_
        have : T (0 : ℝ) b = 0 := by
          funext i
          show θ 0 * b i = 0
          rw [hθ0, zero_mul]
        simpa [this] using hU
      exact (hB.eventually_forall_of_forall_eventually h0).filter_mono nhdsWithin_le_nhds)
    (fun i => algebraMap F (Ainf F) (x0 i)) φ hφ hφs
  rw [hcard] at key

  let f : latCoset I x0 → Λ := fun x => ⟨fun i => algebraMap F (Ainf F) (x.1 i - x0 i), fun i _ => by
    obtain ⟨y, hy, e⟩ := x.2 i
    refine AddSubgroup.mem_map.2 ⟨y, hy, ?_⟩
    show algebraMap F (Ainf F) (y : F) = algebraMap F (Ainf F) (x.1 i - x0 i)
    rw [e]⟩
  have hf : Function.Bijective f := by
    constructor
    · intro x x' h
      refine Subtype.ext (funext fun i => ?_)
      have h1 := hg (congrFun (congrArg Subtype.val h) i)
      exact sub_left_injective h1
    · rintro ⟨l, hl⟩
      have hy : ∀ i, ∃ y ∈ I, j y = l i := fun i => by
        obtain ⟨y, hy, e⟩ := AddSubgroup.mem_map.1 (hl i (Set.mem_univ i))
        exact ⟨y, hy, e⟩
      choose y hyI hyl using hy
      refine ⟨⟨fun i => x0 i + (y i : F), fun i => ⟨y i, hyI i, by simp⟩⟩, Subtype.ext (funext fun i => ?_)⟩
      show algebraMap F (Ainf F) (x0 i + (y i : F) - x0 i) = l i
      rw [add_sub_cancel_left, ← hyl]
      rfl
  let e : latCoset I x0 ≃ Λ := Equiv.ofBijective f hf
  have hterm : ∀ (ε : ℝ) (x : latCoset I x0), φ (fun i => θ ε * algebraMap F (Ainf F) (x.1 i)) =
      φ (T ε ((fun i => algebraMap F (Ainf F) (x0 i)) + (e x : ι → Ainf F))) := by
    intro ε x
    congr 1
    funext i
    show _ = θ ε * (algebraMap F (Ainf F) (x0 i) + algebraMap F (Ainf F) (x.1 i - x0 i))
    rw [← map_add (f := _), add_sub_cancel]
  constructor
  · intro ε hε
    have h1 := (e.summable_iff (f := fun l : Λ => φ (T ε ((fun i => algebraMap F (Ainf F) (x0 i)) + l)))).2 (key.1 ε hε)
    refine h1.congr fun x => ?_
    exact (hterm ε x).symm
  · refine key.2.congr fun ε => ?_
    congr 1
    rw [← e.tsum_eq]
    exact tsum_congr fun x => (hterm ε x).symm
end
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompanionTheory.LocBC

variable {R R' : Type} [CommRing R] [CommRing R'] {C C' : Type 1} [Category.{0} C] [Category.{0} C']
  {Φ : PDF R C} {Φ' : PDF R' C'} {σ : R →+* R'} (m : SMor Φ Φ' σ)

theorem sqC_add {c c' c'' : R'} (hc : c'' = c + c') {a b : IdF Φ.A} {a' b' : IdF Φ'.A}
    (ha : m.LeC c a a') (hb : m.LeC c b b') (ha' : m.LeC c' a a') (hb' : m.LeC c' b b')
    (ha'' : m.LeC c'' a a') (hb'' : m.LeC c'' b b') (T : C') (x : sqM a b (m.G.obj T)) :
    (m.sqC c'' ha'' hb'').τ T x = (m.sqC c ha hb).τ T x + (m.sqC c' ha' hb').τ T x := by
  subst hc
  obtain ⟨x, hx⟩ := x
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
  refine Subtype.ext ?_
  change Ideal.Quotient.mk _ (algebraMap R' _ (c + c') * m.ρ T y) =
    Ideal.Quotient.mk _ (algebraMap R' _ c * m.ρ T y) + Ideal.Quotient.mk _ (algebraMap R' _ c' * m.ρ T y)
  rw [map_add (f := _), add_mul, map_add (f := _)]

theorem sqC_smul {c c' : R'} (r : R) (hc : c' = σ r * c) {a b : IdF Φ.A} {a' b' : IdF Φ'.A}
    (ha : m.LeC c a a') (hb : m.LeC c b b') (ha' : m.LeC c' a a') (hb' : m.LeC c' b b') (T : C')
    (x : sqM a b (m.G.obj T)) :
    (m.sqC c' ha' hb').τ T x = (m.sqC c ha hb).τ T (r • x) := by
  subst hc
  rw [LinearMap.map_smulₛₗ]
  obtain ⟨x, hx⟩ := x
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
  refine Subtype.ext ?_
  change Ideal.Quotient.mk _ (algebraMap R' _ (σ r * c) * m.ρ T y) =
    σ r • Ideal.Quotient.mk _ (algebraMap R' _ c * m.ρ T y)
  have h : ∀ z : Φ'.A.obj T, Ideal.Quotient.mk (b'.S T) (algebraMap R' _ (σ r) * z) = σ r • Ideal.Quotient.mk (b'.S T) z :=
    fun z => by rw [← Algebra.smul_def]; rfl
  rw [← h, ← mul_assoc, ← map_mul]

section Pts

variable {d : ℕ} (E : Frame (Φ := Φ) d) (E' : Frame (Φ := Φ') d) (e : E.D ⟶ m.G.obj E'.D)

theorem mPt_add {c c' c'' : R'} (hc : c'' = c + c') {a b : IdF Φ.A} {a' b' : IdF Φ'.A}
    (ha : m.LeC c a a') (hb : m.LeC c b b') (ha' : m.LeC c' a a') (hb' : m.LeC c' b b')
    (ha'' : m.LeC c'' a a') (hb'' : m.LeC c'' b b') (j : ℕ) (x : CH.H (Pt.U E ⋙ sq a b) j) :
    (mPt m E E' e c'' ha'' hb'').pull j x = (mPt m E E' e c ha hb).pull j x + (mPt m E E' e c' ha' hb').pull j x := by
  obtain ⟨f, hf, rfl⟩ := (CrystallineSemistableComparison.P.cls_surj (CH.cx _) j).1 x
  have h1 := CrystallineSemistableComparison.CechClassBoundaries.cyc (mPt m E E' e c'' ha'' hb'').hom f hf
  have h2 := CrystallineSemistableComparison.CechClassBoundaries.cyc (mPt m E E' e c ha hb).hom f hf
  have h3 := CrystallineSemistableComparison.CechClassBoundaries.cyc (mPt m E E' e c' ha' hb').hom f hf
  change (mPt m E E' e c'' ha'' hb'').hom.mapH j _ = (mPt m E E' e c ha hb).hom.mapH j _ + (mPt m E E' e c' ha' hb').hom.mapH j _
  rw [CrystallineSemistableComparison.P.mapH_cls _ j f hf h1, CrystallineSemistableComparison.P.mapH_cls _ j f hf h2, CrystallineSemistableComparison.P.mapH_cls _ j f hf h3,
    ← (CrystallineSemistableComparison.P.cls_surj _ j).2.2.2.1 _ _ h2 h3 (by rw [map_add (f := _), h2, h3, add_zero])]
  exact cls_congr (funext fun s => sqC_add m hc ha hb ha' hb' ha'' hb'' _ _) _ _

theorem mPt_smul {c c' : R'} (r : R) (hc : c' = σ r * c) {a b : IdF Φ.A} {a' b' : IdF Φ'.A}
    (ha : m.LeC c a a') (hb : m.LeC c b b') (ha' : m.LeC c' a a') (hb' : m.LeC c' b b')
    (j : ℕ) (x : CH.H (Pt.U E ⋙ sq a b) j) :
    (mPt m E E' e c' ha' hb').pull j x = (mPt m E E' e c ha hb).pull j (r • x) := by
  obtain ⟨f, hf, rfl⟩ := (CrystallineSemistableComparison.P.cls_surj (CH.cx _) j).1 x
  have h0 : CH.d _ j (r • f) = 0 := by rw [map_smul]; exact (show r • CH.d _ j f = 0 by rw [show CH.d _ j f = 0 from hf, smul_zero])
  have h1 := CrystallineSemistableComparison.CechClassBoundaries.cyc (mPt m E E' e c' ha' hb').hom f hf
  have h2 := CrystallineSemistableComparison.CechClassBoundaries.cyc (mPt m E E' e c ha hb).hom (r • f) h0
  rw [← (CrystallineSemistableComparison.P.cls_surj _ j).2.2.2.2 r f hf h0]
  change (mPt m E E' e c' ha' hb').hom.mapH j _ = (mPt m E E' e c ha hb).hom.mapH j _
  rw [CrystallineSemistableComparison.P.mapH_cls _ j f hf h1, CrystallineSemistableComparison.P.mapH_cls _ j _ h0 h2]
  exact cls_congr (funext fun s => sqC_smul m r hc ha hb ha' hb' _ _) _ _

theorem pull_U (c : R') {a b : IdF Φ.A} {a' b' : IdF Φ'.A} (ha : m.LeC c a a') (hb : m.LeC c b b') (j : ℕ)
    (x : CH.H (sq a b) j) :
    (mPt m E E' e c ha hb).pull j ((CH.Mor.restrict (sq a b) (Pt.U E)).pull j x) =
      (CH.Mor.restrict (sq a' b') (Pt.U E')).pull j ((m.sqC c ha hb).pull j x) := by
  obtain ⟨f, hf, rfl⟩ := (CrystallineSemistableComparison.P.cls_surj (CH.cx _) j).1 x
  rfl

end Pts

section HAdd

variable {R'' : Type} [CommRing R''] [Algebra R R''] {Ψ : PDF R'' C'} (p : SMor Φ Ψ (algebraMap R R''))
  {d : ℕ} (E : Frame (Φ := Φ) d) (E' : Frame (Φ := Ψ) d) (e : E.D ⟶ p.G.obj E'.D)

theorem hadd_Pt {N : Type} [AddCommGroup N] [Module R N] (ν : N →ₗ[R] R'') {a b : IdF Φ.A} {a' b' : IdF Ψ.A}
    (ha : ∀ n, p.LeC (ν n) a a') (hb : ∀ n, p.LeC (ν n) b b') (j : ℕ) :
    ∃ F : N ⊗[R] CH.H (Pt.U E ⋙ sq a b) j →+ CH.H (Pt.U E' ⋙ sq a' b') j,
      ∀ n x, F (n ⊗ₜ x) = (mPt p E E' e (ν n) (ha n) (hb n)).pull j x := by
  let f : N →+ (CH.H (Pt.U E ⋙ sq a b) j →+ CH.H (Pt.U E' ⋙ sq a' b') j) :=
    AddMonoidHom.mk' (fun n => ((mPt p E E' e (ν n) (ha n) (hb n)).pull j).toAddMonoidHom) (fun n n' => AddMonoidHom.ext fun x =>
      mPt_add p E E' e (map_add ν n n') (ha n) (hb n) (ha n') (hb n') (ha _) (hb _) j x)
  refine ⟨TensorProduct.liftAddHom f fun r n x => ?_, fun n x => ?_⟩
  · exact mPt_smul p E E' e r (by rw [map_smul, Algebra.smul_def]) (ha n) (hb n) (ha _) (hb _) j x
  · exact TensorProduct.liftAddHom_tmul _ _ _ _

end HAdd

end GlobalTheory.CompanionTheory.LocBC
end
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris ReciprocityTheory.ChartRestriction.G.Geo.Tor CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.ConeEval

theorem ev_rs_eq : ∀ {K : Type} [CommRing K] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of K)} (T : Thick (smFun X q))
    {V W : X.Opens} (h : V ≤ W) (hT : InU V T) (hT' : InU W T) (s : Γ(X, W)), ev T hT (rs h s) = ev T hT' s := by
  intro K _ X q T V W h hT hT' s
  have e : X.presheaf.map (homOfLE h).op ≫ (pt T).appLE V ⊤ hT = (pt T).appLE W ⊤ hT' :=
    Scheme.Hom.map_appLE _ _ _
  unfold ev rs GlobalTheory.Cris.evalAt
  rw [← e]
  rfl

end GlobalTheory.CompanionTheory.ConeEval
end
