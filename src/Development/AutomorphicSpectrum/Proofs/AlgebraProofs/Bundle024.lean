module

public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle003
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.RingTheory.Valuation.Integers
import Mathlib.Algebra.Module.StablyFree.Basic
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsSplitGaussChars
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle017
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.NumberTheory.NumberField.Discriminant.Defs
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LatNormGrLatNeZeroOfSpan
public import Mathlib.Algebra.Module.Lattice.Basic
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle020
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle013
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle019
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle021
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
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
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsTight
public import Mathlib.RingTheory.Flat.TorsionFree
import ReciprocityTheory.DualLattices.Bundle007
import ReciprocityTheory.DualLattices.Bundle002
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.GermComp1ZeroPointLeft
public import Mathlib.Algebra.Algebra.Hom.Rat
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle002
import Development.AutomorphicSpectrum.PublishedTheorems.Algebra₂.RegularHypothesesAndConclusion

@[expose] public section

section

open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.CompanionTheory.Relay.torsion_points_finite_flat_subgroup : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G], ∀ (T : TorsRep G p) (N : Type) [AddCommGroup N] [Fintype N] [DecidableEq N] (pt : N → (sp (R₀ := R) R ⟶ G)), IsTorsPts G p pt → ∀ K : AddSubgroup N, IsFinFlatSub G (T.A ⧸ vanIdeal T pt K) (spMap (Ideal.Quotient.mkₐ R (vanIdeal T pt K)) ≫ T.y) := by
  classical
  intro p _ C _ _ _ v R _ _ hv hp G _ _ T N _ _ _ pt hpt K
  haveI : IsDomain R := Function.Injective.isDomain (algebraMap R C) hv.hom_inj
  haveI : ValuationRing R := ValuationRing.iff_dvd_total.mpr ⟨fun a b => by
    rcases le_total (v (algebraMap R C a)) (v (algebraMap R C b)) with h | h
    · exact Or.inr (hv.dvd_of_le h)
    · exact Or.inl (hv.dvd_of_le h)⟩
  haveI : IsLocalRing R := ValuationRing.isLocalRing R
  haveI : IsBezout R := ValuationRing.instIsBezout
  haveI : Module.Finite R T.A := T.fin
  set I : Ideal T.A := vanIdeal T pt (K : Set N) with hI
  have hpts : ∀ x : N, pt x ^ p = 1 := fun x => (hpt.range (pt x)).mpr ⟨x, rfl⟩
  choose ev hev using fun x : N => (T.univ R (pt x) (hpts x)).exists
  have huniq : ∀ (x : N) (φ : T.A →ₐ[R] R), spMap φ ≫ T.y = pt x → φ = ev x :=
    fun x φ h => (T.univ R (pt x) (hpts x)).unique h (hev x)
  have memI : ∀ a : T.A, a ∈ I ↔ ∀ k ∈ K, ev k a = 0 := by
    intro a
    constructor
    · intro ha k hk
      have ha' : ∀ k ∈ (K : Set N), ∀ φ : T.A →ₐ[R] R, spMap φ ≫ T.y = pt k → φ a = 0 := ha
      exact ha' k hk (ev k) (hev k)
    · intro ha
      show ∀ k ∈ (K : Set N), ∀ φ : T.A →ₐ[R] R, spMap φ ≫ T.y = pt k → φ a = 0
      intro k hk φ hφ
      rw [huniq k φ hφ]
      exact ha k hk
  obtain ⟨evbar, hevbar⟩ : ∃ e : K → ((T.A ⧸ I) →ₐ[R] R),
      ∀ k, (e k).comp (Ideal.Quotient.mkₐ R I) = ev k :=
    ⟨fun k => Ideal.Quotient.liftₐ I (ev k) (fun a ha => (memI a).mp ha k k.2),
      fun k => Ideal.Quotient.liftₐ_comp _ _ _⟩
  have hsep1 : ∀ b : T.A ⧸ I, (∀ k : K, evbar k b = 0) → b = 0 := by
    intro b hb
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mkₐ_surjective R I b
    rw [Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem, memI]
    intro k hk
    have h1 := hb ⟨k, hk⟩
    rw [← AlgHom.comp_apply, hevbar] at h1
    exact h1
  have htors : Submodule.torsion R (T.A ⧸ I) = ⊥ := by
    rw [eq_bot_iff]
    intro b hb
    obtain ⟨r, hr⟩ := (Submodule.mem_torsion_iff b).mp hb
    rw [Submodule.mem_bot]
    refine hsep1 b fun k => ?_
    have h1 := congrArg (evbar k) hr
    rw [map_zero, Submonoid.smul_def, map_smul, smul_eq_mul] at h1
    exact (mul_eq_zero.mp h1).resolve_left (nonZeroDivisors.coe_ne_zero r)
  haveI : Module.Flat R (T.A ⧸ I) := (Module.Flat.flat_iff_torsion_eq_bot_of_isBezout).mpr htors
  haveI : Module.Finite R (T.A ⧸ I) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ R I).toLinearMap (Ideal.Quotient.mkₐ_surjective R I)
  haveI : Module.Free R (T.A ⧸ I) := Module.free_of_flat_of_isLocalRing
  have h0 : pt 0 = 1 := mul_left_cancel (a := pt 0) (by rw [_root_.mul_one, ← hpt.add, add_zero])
  have hneg : ∀ x, pt (-x) = (pt x)⁻¹ := fun x =>
    eq_inv_of_mul_eq_one_left (by rw [← hpt.add, neg_add_cancel, h0])
  have hE : ∀ k : K, spMap (evbar k) ≫ spMap (Ideal.Quotient.mkₐ R I) ≫ T.y = pt k := by
    intro k
    rw [← Category.assoc, ReciprocityTheory.ChartRestriction.G.Chart.spMap_comp, hevbar, hev]
  have hpowA : ∀ {X : Over (Spec (CommRingCat.of R))} (f : X ⟶ sp (R₀ := R) T.A), (f ≫ T.y) ^ p = 1 :=
    fun f => by rw [← CategoryTheory.MonObj.comp_pow, T.y_p, CategoryTheory.MonObj.comp_one]
  have hu : (spMap (Ideal.Quotient.mkₐ R I) ≫ T.y) ^ p = 1 := hpowA _
  have hpowc : ∀ {X : Over (Spec (CommRingCat.of R))} (f : X ⟶ sp (R₀ := R) (T.A ⧸ I)),
      (f ≫ spMap (Ideal.Quotient.mkₐ R I) ≫ T.y) ^ p = 1 :=
    fun f => by rw [← CategoryTheory.MonObj.comp_pow, hu, CategoryTheory.MonObj.comp_one]
  obtain ⟨Λ, hΛt⟩ : ∃ L : K → K → (TensorProduct R (T.A ⧸ I) (T.A ⧸ I) →ₐ[R] R),
      ∀ k1 k2 x y, L k1 k2 (TensorProduct.tmul R x y) = evbar k1 x * evbar k2 y :=
    ⟨fun k1 k2 => Algebra.TensorProduct.lift (evbar k1) (evbar k2) (fun _ _ => Commute.all _ _),
      fun _ _ _ _ => Algebra.TensorProduct.lift_tmul _ _ _ _ _⟩
  have hΛL : ∀ k1 k2, (Λ k1 k2).comp Algebra.TensorProduct.includeLeft = evbar k1 := fun k1 k2 =>
    AlgHom.ext fun b => by simp [hΛt]
  have hΛR : ∀ k1 k2, (Λ k1 k2).comp Algebra.TensorProduct.includeRight = evbar k2 := fun k1 k2 =>
    AlgHom.ext fun b => by simp [hΛt]
  have hι : Function.Injective (Pi.algHom R (fun _ : K => R) evbar).toLinearMap := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro b hb
    exact hsep1 b fun k => by simpa using congrFun hb k
  have key : ∀ (w : TensorProduct R (T.A ⧸ I) (T.A ⧸ I)) (k1 k2 : K),
      (Pi.algHom R (fun _ : K => R) evbar).toLinearMap
        (TensorProduct.piScalarRight R R (T.A ⧸ I) K
          (((Pi.algHom R (fun _ : K => R) evbar).toLinearMap.lTensor (T.A ⧸ I)) w) k2) k1 =
        Λ k1 k2 w := by
    intro w k1 k2
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul x y => simp [hΛt, TensorProduct.piScalarRight_apply, mul_comm]
    | add x y hx hy => simp only [map_add (f := _), Pi.add_apply, hx, hy]
  have hsep2 : ∀ w : TensorProduct R (T.A ⧸ I) (T.A ⧸ I), (∀ k1 k2 : K, Λ k1 k2 w = 0) → w = 0 := by
    intro w hw
    have h1 : TensorProduct.piScalarRight R R (T.A ⧸ I) K
        (((Pi.algHom R (fun _ : K => R) evbar).toLinearMap.lTensor (T.A ⧸ I)) w) = 0 := by
      funext k2
      apply hι
      funext k1
      rw [key, hw]
      simp
    rw [LinearEquiv.map_eq_zero_iff] at h1
    exact (injective_iff_map_eq_zero _).mp
      (Module.Flat.lTensor_preserves_injective_linearMap _ hι) w h1
  refine ⟨inferInstance, inferInstance, ?_, ?_, ?_, ?_⟩
  · intro S _ _ φ φ' hφ
    have e1 : spMap (φ.comp (Ideal.Quotient.mkₐ R I)) ≫ T.y =
        spMap (φ'.comp (Ideal.Quotient.mkₐ R I)) ≫ T.y := by
      rw [← ReciprocityTheory.ChartRestriction.G.Chart.spMap_comp, ← ReciprocityTheory.ChartRestriction.G.Chart.spMap_comp, Category.assoc,
        Category.assoc, hφ]
    have e2 := (T.univ S _ (hpowA (spMap (φ.comp (Ideal.Quotient.mkₐ R I))))).unique rfl e1.symm
    refine AlgHom.ext fun b => ?_
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mkₐ_surjective R I b
    exact DFunLike.congr_fun e2 a
  · intro S _ _
    refine ⟨(Algebra.ofId R S).comp (evbar 0), ?_⟩
    rw [← ReciprocityTheory.ChartRestriction.G.Chart.spMap_comp, Category.assoc, hE]
    show spMap (Algebra.ofId R S) ≫ pt 0 = 1
    rw [h0, CategoryTheory.MonObj.comp_one]
  · have hm : ((spMap (Algebra.TensorProduct.includeLeft : (T.A ⧸ I) →ₐ[R] TensorProduct R (T.A ⧸ I) (T.A ⧸ I)) ≫
          spMap (Ideal.Quotient.mkₐ R I) ≫ T.y) *
        (spMap (Algebra.TensorProduct.includeRight : (T.A ⧸ I) →ₐ[R] TensorProduct R (T.A ⧸ I) (T.A ⧸ I)) ≫
          spMap (Ideal.Quotient.mkₐ R I) ≫ T.y)) ^ p = 1 := by
      rw [mul_pow, hpowc, hpowc, _root_.one_mul]
    obtain ⟨ψ0, hψ0⟩ := (T.univ _ _ hm).exists
    have hψI : ∀ a ∈ I, ψ0 a = 0 := by
      intro a ha
      refine hsep2 _ fun k1 k2 => ?_
      have e : spMap ((Λ k1 k2).comp ψ0) ≫ T.y = pt ((k1 : N) + k2) := by
        rw [← ReciprocityTheory.ChartRestriction.G.Chart.spMap_comp, Category.assoc, hψ0, CategoryTheory.MonObj.comp_mul,
          ← Category.assoc (spMap (Λ k1 k2)) (spMap Algebra.TensorProduct.includeLeft),
          ReciprocityTheory.ChartRestriction.G.Chart.spMap_comp, hΛL, hE,
          ← Category.assoc (spMap (Λ k1 k2)) (spMap Algebra.TensorProduct.includeRight),
          ReciprocityTheory.ChartRestriction.G.Chart.spMap_comp, hΛR, hE, hpt.add]
      rw [← AlgHom.comp_apply, huniq _ _ e]
      exact (memI a).mp ha _ (K.add_mem k1.2 k2.2)
    intro S _ _ φ φ'
    have hLR : (Algebra.TensorProduct.lift φ φ' (fun _ _ => Commute.all _ _)).comp
        Algebra.TensorProduct.includeRight = φ' := AlgHom.ext fun b => by simp
    refine ⟨(Algebra.TensorProduct.lift φ φ' (fun _ _ => Commute.all _ _)).comp
      (Ideal.Quotient.liftₐ I ψ0 hψI), ?_⟩
    rw [← ReciprocityTheory.ChartRestriction.G.Chart.spMap_comp, Category.assoc,
      ← Category.assoc (spMap (Ideal.Quotient.liftₐ I ψ0 hψI)), ReciprocityTheory.ChartRestriction.G.Chart.spMap_comp,
      Ideal.Quotient.liftₐ_comp, hψ0, CategoryTheory.MonObj.comp_mul]
    rw [← Category.assoc (spMap (Algebra.TensorProduct.lift φ φ' (fun _ _ => Commute.all _ _)))
        (spMap Algebra.TensorProduct.includeLeft),
      ReciprocityTheory.ChartRestriction.G.Chart.spMap_comp, Algebra.TensorProduct.lift_comp_includeLeft,
      ← Category.assoc (spMap (Algebra.TensorProduct.lift φ φ' (fun _ _ => Commute.all _ _)))
        (spMap Algebra.TensorProduct.includeRight),
      ReciprocityTheory.ChartRestriction.G.Chart.spMap_comp, hLR]
  · have hinv : ((spMap (Ideal.Quotient.mkₐ R I) ≫ T.y)⁻¹) ^ p = 1 := by rw [inv_pow, hu, inv_one]
    obtain ⟨ψ0, hψ0⟩ := (T.univ (T.A ⧸ I) _ hinv).exists
    have hψI : ∀ a ∈ I, ψ0 a = 0 := by
      intro a ha
      refine hsep1 _ fun k => ?_
      have e : spMap ((evbar k).comp ψ0) ≫ T.y = pt (-(k : N)) := by
        rw [← ReciprocityTheory.ChartRestriction.G.Chart.spMap_comp, Category.assoc, hψ0, CategoryTheory.GrpObj.comp_inv,
          hE, hneg]
      rw [← AlgHom.comp_apply, huniq _ _ e]
      exact (memI a).mp ha _ (K.neg_mem k.2)
    intro S _ _ φ
    refine ⟨φ.comp (Ideal.Quotient.liftₐ I ψ0 hψI), ?_⟩
    rw [← ReciprocityTheory.ChartRestriction.G.Chart.spMap_comp, Category.assoc,
      ← Category.assoc (spMap (Ideal.Quotient.liftₐ I ψ0 hψI)), ReciprocityTheory.ChartRestriction.G.Chart.spMap_comp,
      Ideal.Quotient.liftₐ_comp, hψ0, CategoryTheory.GrpObj.comp_inv, inv_mul_cancel]
end

section

open GlobalTheory.CompanionTheory.Ar.Crv

theorem _root_.GlobalTheory.T.sub_and_quotient_bundles : ∀ (K : Type) [Field K] (C : ACurve K) (V : Type) [AddCommGroup V] [Module K V] [FiniteDimensional K V] (L : C.I → AddSubgroup V) (W : Submodule K V), IsBun C L → IsBun C (sub C L W) ∧ IsBun C (quot C L W) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Crv.SubQuot.isBun_sub_quot | exact GlobalTheory.CompanionTheory.Ar.Crv.SubQuot.isBun_sub_quot | (intros; apply GlobalTheory.CompanionTheory.Ar.Crv.SubQuot.isBun_sub_quot <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.Conj.SplitDisc

open Module

theorem injective_of_charZero (E : Type) [Field E] [NumberField E] {L : Type} [Field L] [CharZero L]
    (g : 𝓞 E →+* L) : Function.Injective g := by
  refine (injective_iff_map_eq_zero g).2 fun x hx => ?_
  by_contra h
  have hne := Ideal.comap_ne_bot_of_integral_mem (R := ℤ) (I := RingHom.ker g) h
    (RingHom.mem_ker.2 hx) (Algebra.IsIntegral.isIntegral x)
  apply hne
  rw [eq_bot_iff]
  intro n hn
  have h0 : g (algebraMap ℤ (𝓞 E) n) = 0 := RingHom.mem_ker.1 (Ideal.mem_comap.1 hn)
  have h1 : (n : L) = 0 := by simpa using h0
  simpa using h1

theorem det_sq_eq_discr (E : Type) [Field E] [NumberField E] (R S : Type) [CommRing R] [IsDomain R] [CharZero R]
    [Fintype S] [DecidableEq S] (σ : S → (𝓞 E →+* R)) (hσ : Function.Injective σ)
    (hc : Fintype.card S = finrank ℚ E) (e : Free.ChooseBasisIndex ℤ (𝓞 E) ≃ S) :
    (Matrix.of fun i j => σ (e j) (RingOfIntegers.basis E i)).det ^ 2 = (NumberField.discr E : R) := by
  let F := FractionRing R
  let Ω := AlgebraicClosure F
  let i₀ : R →+* Ω := (algebraMap F Ω).comp (algebraMap R F)
  have hi₀ : Function.Injective i₀ :=
    (algebraMap F Ω).injective.comp (IsFractionRing.injective R F)
  have : CharZero Ω := charZero_of_injective_ringHom hi₀
  let ρ : S → (𝓞 E →+* Ω) := fun s => i₀.comp (σ s)
  have hρ : ∀ s, Function.Injective (ρ s) := fun s => injective_of_charZero E (ρ s)
  let τ : S → (E →ₐ[ℚ] Ω) := fun s => (IsFractionRing.lift (hρ s)).toRatAlgHom
  have hτ : ∀ s (a : 𝓞 E), τ s (algebraMap (𝓞 E) E a) = i₀ (σ s a) := fun s a => by
    change IsFractionRing.lift (hρ s) (algebraMap (𝓞 E) E a) = _
    rw [IsFractionRing.lift_algebraMap]
    rfl
  have hinj : Function.Injective τ := by
    intro s t hst
    apply hσ
    ext a
    apply hi₀
    rw [← hτ, ← hτ, hst]
  have hbij : Function.Bijective τ :=
    (Fintype.bijective_iff_injective_and_card _).2 ⟨hinj, by rw [AlgHom.card, hc]⟩
  let e' : Free.ChooseBasisIndex ℤ (𝓞 E) ≃ (E →ₐ[ℚ] Ω) := e.trans (Equiv.ofBijective τ hbij)
  have key := Algebra.discr_eq_det_embeddingsMatrixReindex_pow_two ℚ Ω (integralBasis E) e'
  rw [← coe_discr] at key
  have hm : Algebra.embeddingsMatrixReindex ℚ Ω (integralBasis E) e' =
      (Matrix.of fun i j => σ (e j) (RingOfIntegers.basis E i)).map i₀ := by
    ext i j
    simp only [Algebra.embeddingsMatrixReindex, Algebra.embeddingsMatrix, Matrix.reindex_apply,
      Matrix.submatrix_apply, Matrix.of_apply, Matrix.map_apply, integralBasis_apply]
    exact hτ _ _
  rw [hm, ← RingHom.mapMatrix_apply, ← RingHom.map_det, ← map_pow] at key
  apply hi₀
  rw [← key]
  simp

theorem isSplit_of_det {O k S ι : Type} [CommRing O] [Field k] [Fintype S] [DecidableEq S] [Fintype ι] [DecidableEq ι]
    (χ : S → (O →+* k)) (b : Basis ι ℤ O) (e : ι ≃ S)
    (h : (Matrix.of fun i j => χ (e j) (b i)).det ≠ 0) : IsSplit χ := by
  unfold IsSplit
  let B := Algebra.TensorProduct.basis k b
  let B' := (Pi.basisFun k S).reindex e.symm
  let f := (Algebra.TensorProduct.lift (Algebra.ofId k (S → k)) (AlgHom.pi fun s => (χ s).toIntAlgHom)
    (fun _ _ => Commute.all _ _))
  have hm : LinearMap.toMatrix B B' f.toLinearMap = (Matrix.of fun i j => χ (e j) (b i)).transpose := by
    ext i j
    simp [LinearMap.toMatrix_apply, B, B', f]
  have hu : IsUnit (LinearMap.toMatrix B B' f.toLinearMap).det := by
    rw [hm, Matrix.det_transpose]
    exact isUnit_iff_ne_zero.2 h
  exact (LinearEquiv.ofIsUnitDet hu).bijective

theorem exists_isSplit (E : Type) [Field E] [NumberField E] (R K S : Type) [CommRing R] [IsDomain R] [CharZero R]
    [Field K] [Fintype S] (p : ℕ) [Fact p.Prime] [Algebra (ZMod p) K] (σ : S → (𝓞 E →+* R)) (π : R →+* K)
    (hσ : Function.Injective σ) (hc : Fintype.card S = finrank ℚ E) (hp : ¬ (p : ℤ) ∣ NumberField.discr E) :
    ∃ χ : S → (𝓞 E →+* algebraicClosure (ZMod p) K), IsSplit χ ∧
      ∀ s a, ((χ s a : algebraicClosure (ZMod p) K) : K) = π (σ s a) := by
  classical
  have hchar : CharP K p := charP_of_injective_algebraMap (algebraMap (ZMod p) K).injective p
  have hmem : ∀ s a, (π.comp (σ s)) a ∈ algebraicClosure (ZMod p) K := fun s a => by
    have h1 : IsIntegral ℤ ((π.comp (σ s)) a) :=
      (Algebra.IsIntegral.isIntegral (R := ℤ) a).map (π.comp (σ s)).toIntAlgHom
    exact mem_algebraicClosure_iff'.2 (h1.tower_top)
  let χ : S → (𝓞 E →+* algebraicClosure (ZMod p) K) := fun s =>
    (π.comp (σ s)).codRestrict (algebraicClosure (ZMod p) K) (hmem s)
  refine ⟨χ, ?_, fun s a => rfl⟩
  have hcard : Fintype.card (Free.ChooseBasisIndex ℤ (𝓞 E)) = Fintype.card S := by
    rw [hc, finrank_eq_card_basis (integralBasis E)]
  let e : Free.ChooseBasisIndex ℤ (𝓞 E) ≃ S := Fintype.equivOfCardEq hcard
  refine isSplit_of_det χ (RingOfIntegers.basis E) e fun h0 => hp ?_
  have hsq := congrArg π (det_sq_eq_discr E R S σ hσ hc e)
  have hmap : (algebraMap (algebraicClosure (ZMod p) K) K).mapMatrix
      (Matrix.of fun i j => χ (e j) (RingOfIntegers.basis E i)) =
      π.mapMatrix (Matrix.of fun i j => σ (e j) (RingOfIntegers.basis E i)) := by
    ext i j
    rfl
  have hdet : π (Matrix.of fun i j => σ (e j) (RingOfIntegers.basis E i)).det = 0 := by
    rw [RingHom.map_det, ← hmap, ← RingHom.map_det]
    simp [h0]
  rw [map_pow, hdet] at hsq
  have hz : ((NumberField.discr E : ℤ) : K) = 0 := by
    simpa using hsq.symm
  exact (CharP.intCast_eq_zero_iff K p _).1 hz

end GlobalTheory.CompanionTheory.Ar.Conj.SplitDisc
end
end

section

namespace GlobalTheory.CompanionTheory.Ar.HT

open Module NumberField

theorem exists_smul_mem_of_mem_span_val {C : Type} [Field C] {v : Valuation C NNReal} {O : Type}
    [CommRing O] [Algebra O C] (hv : v.Integers O) {V : Type} [AddCommGroup V] [Module C V]
    [Module O V] [IsScalarTower O C V] (L : Submodule O V) {u : V}
    (hu : u ∈ Submodule.span C (L : Set V)) : ∃ c : C, c ≠ 0 ∧ c • u ∈ L := by
  have key : ∀ (a b : C) (x : V), b ≠ 0 → v a ≤ v b → b • x ∈ L → a • x ∈ L := by
    intro a b x hb hab hx
    have hvb : 0 < v b := (Valuation.pos_iff v).2 hb
    have h1 : v (a / b) ≤ 1 := by
      rw [map_div₀]
      exact (div_le_one hvb).2 hab
    obtain ⟨o, ho⟩ := hv.exists_of_le_one h1
    have h2 : a • x = o • (b • x) := by
      rw [← IsScalarTower.algebraMap_smul C o, ho, smul_smul, div_mul_cancel₀ _ hb]
    rw [h2]
    exact L.smul_mem o hx
  induction hu using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by simpa using hx⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha, hx⟩ := hx
    obtain ⟨b, hb, hy⟩ := hy
    rcases le_total (v a) (v b) with h | h
    · exact ⟨a, ha, by rw [smul_add]; exact L.add_mem hx (key a b y hb h hy)⟩
    · exact ⟨b, hb, by rw [smul_add]; exact L.add_mem (key b a x ha h hx) hy⟩
  | smul d x _ hx =>
    obtain ⟨a, ha, hx⟩ := hx
    by_cases hd : d = 0
    · exact ⟨1, one_ne_zero, by simp [hd]⟩
    · exact ⟨a / d, div_ne_zero ha hd, by rw [smul_smul, div_mul_cancel₀ _ hd]; exact hx⟩

theorem latIn_isLattice : ∀ (C : Type) [Field C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] (hv : v.Integers O) (V : Type) [AddCommGroup V] [Module C V] [Module O V] [IsScalarTower O C V] (L : Submodule O V) (U : Submodule C V), L.FG → U ≤ Submodule.span C (L : Set V) → (latIn L U).IsLattice C := by
  intro C _ v O _ _ hv V _ _ _ _ L U hL hU
  have hfg := GlobalTheory.CompanionTheory.Ar.HT.fg_inf_restrictScalars_of_integers C v O hv V L U hL
  refine ⟨?_, ?_⟩
  · have hinj : Function.Injective (U.subtype.restrictScalars O) := Subtype.val_injective
    apply Submodule.fg_of_fg_map_injective (U.subtype.restrictScalars O) hinj
    convert hfg using 1
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨hy, y.2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨⟨x, h2⟩, h1, rfl⟩
  · intro s hs hli
    letI : IsFractionRing O C := hv.isFractionRing
    exact (LinearIndependent.iff_fractionRing _ _).mp hli
end GlobalTheory.CompanionTheory.Ar.HT
end

section

open GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Flat.DegCurve

theorem _root_.GlobalTheory.T.module_basis_lattice_bundle_free : ∀ (K : Type) [Field K] (C : ACurve K) (V : Type) [AddCommGroup V] [Module K V] [FiniteDimensional K V] (L : C.I → AddSubgroup V) (O ι k : Type) [CommRing O] [Fintype ι] [Field k] [Algebra k K] (b : Module.Basis ι ℤ O) (ρ : O →+* Module.End K V) (r : ℕ) (i : C.I), IsBun C L → (∀ c : k, C.v i (algebraMap k K c) ≤ 1) → (∃ x : Fin r → V, LinearIndependent K (fun q : Fin r × ι => ρ (b q.2) (x q.1)) ∧ ∀ y, y ∈ L i ↔ ∃ c : Fin r × ι → K, (∀ q, C.v i (c q) ≤ 1) ∧ y = ∑ q, c q • ρ (b q.2) (x q.1)) → FreeAt C k (act k ρ) L r i := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.DegCurve.freeAt_of_basis_lattice | exact GlobalTheory.CompanionTheory.Ar.Flat.DegCurve.freeAt_of_basis_lattice | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.DegCurve.freeAt_of_basis_lattice <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.FreeQuotProof GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.FreeQuot GlobalTheory.CompanionTheory.FreeQuotGlue

namespace GlobalTheory.CompanionTheory.FreeQuotGlue

theorem IsChart.exists_opens_image_preimage {P X Y : Scheme.{0}} {a b : P ⟶ X} {V : X.Opens}
    {q : V.toScheme ⟶ Y} (h : IsChart a b V q) (V' : X.Opens) (hV : V' ≤ V)
    (hs : a ⁻¹ᵁ V' = b ⁻¹ᵁ V') : ∃ D : Y.Opens, V.ι ''ᵁ (q ⁻¹ᵁ D) = V' := by
  have := h.isFinite
  have hsat : ∀ u v : V.toScheme, q u = q v → V.ι u ∈ V' → V.ι v ∈ V' := by
    intro u v huv hu
    obtain ⟨p, hpa, hpb⟩ := (h.apply_eq_iff u v).1 huv
    have hp : p ∈ a ⁻¹ᵁ V' := by
      show a p ∈ V'
      rw [hpa]
      exact hu
    rw [hs] at hp
    have hb : b p ∈ V' := hp
    rwa [hpb] at hb
  let C : Set V.toScheme := ((V.ι ⁻¹ᵁ V' : V.toScheme.Opens) : Set V.toScheme)ᶜ
  have hC : IsClosed C := (V.ι ⁻¹ᵁ V').isOpen.isClosed_compl
  have hqC : IsClosed (q '' C) := q.isClosedMap C hC
  refine ⟨⟨(q '' C)ᶜ, hqC.isOpen_compl⟩, ?_⟩
  ext x
  constructor
  · rintro ⟨u, hu, rfl⟩
    by_contra hx
    exact hu ⟨u, hx, rfl⟩
  · intro hx
    obtain ⟨u, rfl⟩ : ∃ u, V.ι u = x := by
      rw [← Set.mem_range, Scheme.Opens.range_ι]
      exact hV hx
    refine ⟨u, ?_, rfl⟩
    rintro ⟨v, hv, hvu⟩
    exact hv (hsat u v hvu.symm hx)

end GlobalTheory.CompanionTheory.FreeQuotGlue
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.FreeQuotProof GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.FreeQuot


theorem _root_.GlobalTheory.T.finite_set_basic_open_affine : ∀ {X : Scheme.{0}} (U V₀ : X.Opens), IsAffineOpen U → V₀ ≤ U → ∀ K : Set X, K.Finite → K ⊆ V₀ → ∃ f : Γ(X, U), K ⊆ X.basicOpen f ∧ X.basicOpen f ≤ V₀ := by
  first | exact @GlobalTheory.CompanionTheory.PrimeAvoid.exists_basicOpen_between | exact GlobalTheory.CompanionTheory.PrimeAvoid.exists_basicOpen_between | (intros; apply GlobalTheory.CompanionTheory.PrimeAvoid.exists_basicOpen_between <;> assumption)
end
