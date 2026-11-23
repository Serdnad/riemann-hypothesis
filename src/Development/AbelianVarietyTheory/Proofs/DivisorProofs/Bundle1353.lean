module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle120
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.RingTheory.Etale.Basic
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUnramifiedExtTorsionPointsGoodReduction
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1203
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1212
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1214
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle149
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorsionFrameIsUnitAlongSection
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ConstOfNormPeriodic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1217
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle041
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorsionValuesCoordsOperatorPermute
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.RingTheory.Etale.StandardEtale
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.TotallySplit
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
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.RingTheory.RootsOfUnity.EnoughRootsOfUnity
import Mathlib.Tactic.TypeStar
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.Definitions.Divisors.TorusExt
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle710
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle012
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.Bundle001

@[expose] public section

section

open IsLocalRing Polynomial

noncomputable local instance (priority := high) algebraicClosureResidueFieldForKummer
    (R : Type) [CommRing R] [IsLocalRing R] :
    Algebra (ResidueField R) (AlgebraicClosure (ResidueField R)) :=
  AlgebraicClosure.instAlgebra (ResidueField R)

namespace GlobalTheory.KummerUnram

theorem etale_adjoinRoot_pow_sub {R : Type} [CommRing R] [Nontrivial R] {k : ℕ} (hk : IsUnit (k : R)) (u : Rˣ) :
    Algebra.Etale R (AdjoinRoot (X ^ k - C (u : R))) := by
  have hk0 : k ≠ 0 := by
    rintro rfl
    exact not_isUnit_zero (M₀ := R) (by simpa using hk)
  have hm : (X ^ k - C (u : R)).Monic := monic_X_pow_sub_C _ hk0
  have h1 : AdjoinRoot.root (X ^ k - C (u : R)) ^ k = algebraMap R _ (u : R) := by
    have := AdjoinRoot.eval₂_root (X ^ k - C (u : R))
    simpa [sub_eq_zero] using this
  have hr : IsUnit (AdjoinRoot.root (X ^ k - C (u : R))) :=
    (isUnit_pow_iff hk0).1 (h1 ▸ (u.isUnit.map _))
  let P : StandardEtalePair R := ⟨X ^ k - C (u : R), hm, derivative (X ^ k - C (u : R)), 1, 0, 1, by simp⟩
  have h : IsUnit (AdjoinRoot.mk (X ^ k - C (u : R)) (derivative (X ^ k - C (u : R)))) := by
    have e : AdjoinRoot.mk (X ^ k - C (u : R)) (derivative (X ^ k - C (u : R))) =
        algebraMap R _ (k : R) * AdjoinRoot.root _ ^ (k - 1) := by
      simp [derivative_X_pow, AdjoinRoot.algebraMap_eq]
    rw [e]
    exact (hk.map _).mul (hr.pow _)
  exact .of_equiv (P.equivAwayAdjoinRoot.trans
    ((IsLocalization.atUnit _ (Localization.Away (AdjoinRoot.mk _ (derivative (X ^ k - C (u : R))))) _
      h).symm.restrictScalars R))

end GlobalTheory.KummerUnram

namespace GlobalTheory.KummerUnram

theorem exists_root_step {F : Type} [Field F] [IsAlgClosed F] (T : Subring F)
    [IsDiscreteValuationRing T] {k : ℕ} (hk : IsUnit (k : T)) (u : Tˣ)
    (ub : AlgebraicClosure (ResidueField T)) (hub : ub ^ k = algebraMap _ _ (residue T u)) :
    ∃ T' : Subring F, UnramSub T.subtype T' ∧ ∃ y ∈ T', y ^ k = ((u : T) : F) ∧
      ∀ n : ℕ, ub ^ n ≠ 1 → y ^ n ≠ 1 := by
  letI : IsLocalRing T := IsDiscreteValuationRing.toIsLocalRing
  have := etale_adjoinRoot_pow_sub hk u
  let ρ : T →+* AlgebraicClosure (ResidueField T) :=
    (algebraMap (ResidueField T) _).comp (residue T)
  let ε : AdjoinRoot (X ^ k - C (u : T)) →+* AlgebraicClosure (ResidueField T) :=
    AdjoinRoot.lift ρ ub (by simp [ρ, hub])
  have hερ : ε.comp (algebraMap T _) = ρ := by
    ext t
    simp [ε, AdjoinRoot.algebraMap_eq]
  have hε : IsLocalHom (ε.comp (algebraMap T (AdjoinRoot (X ^ k - C (u : T))))) := by
    rw [hερ]
    exact RingHom.isLocalHom_comp (algebraMap (ResidueField T) _) (residue T)
  obtain ⟨B, _, _, _, ψ, ρ', j', -, h2, h3, h4, h5⟩ :=
    TorsionUnram.exists_local_of_etale ε hε T.subtype Subtype.val_injective
  obtain ⟨hD, f, hf, hirr⟩ := UnramSub.range (i := j') h3
  refine ⟨j'.range, ⟨hD, f.comp (ψ.comp (algebraMap T _)), fun v => ?_,
    fun π hπ => hirr _ (h5 π hπ)⟩, j' (ψ (AdjoinRoot.root _)), ⟨_, rfl⟩, ?_, fun n hn hy => hn ?_⟩
  · rw [RingHom.comp_apply, hf]
    exact congr($h4 v)
  · have h1 : AdjoinRoot.root (X ^ k - C (u : T)) ^ k = algebraMap T _ (u : T) := by
      have := AdjoinRoot.eval₂_root (X ^ k - C (u : T))
      simpa [sub_eq_zero] using this
    rw [← map_pow, ← map_pow, h1]
    exact congr($h4 (u : T))
  · have e1 : ψ (AdjoinRoot.root (X ^ k - C (u : T))) ^ n = 1 :=
      h3 (by rw [map_pow, hy, map_one])
    have e2 : ρ' (ψ (AdjoinRoot.root (X ^ k - C (u : T)))) = ub := by
      rw [← RingHom.comp_apply, h2]
      simp [ε]
    rw [← e2, ← map_pow, e1, map_one]

end GlobalTheory.KummerUnram

namespace GlobalTheory.KummerUnram

theorem exists_rootsOfUnity {F : Type} [Field F] [IsAlgClosed F] (T : Subring F)
    [IsDiscreteValuationRing T] {k : ℕ} (hk : IsUnit (k : T)) :
    ∃ T' : Subring F, UnramSub T.subtype T' ∧ ∀ z : F, z ^ k = 1 → z ∈ T' := by
  letI : IsLocalRing T := IsDiscreteValuationRing.toIsLocalRing
  let ρ : T →+* AlgebraicClosure (ResidueField T) :=
    (algebraMap (ResidueField T) _).comp (residue T)
  have hkΩ : ((k : ℕ) : AlgebraicClosure (ResidueField T)) ≠ 0 := by
    simpa [ρ] using (hk.map ρ).ne_zero
  have hk0 : 0 < k := Nat.pos_of_ne_zero (by rintro rfl; simp at hkΩ)
  haveI : NeZero ((k : ℕ) : AlgebraicClosure (ResidueField T)) := ⟨hkΩ⟩
  obtain ⟨ub, hub⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (AlgebraicClosure (ResidueField T)) k
  obtain ⟨T', hT', y, hyT, hy, hyn⟩ := exists_root_step T hk 1 ub (by simp [hub.pow_eq_one])
  have hy1 : y ^ k = 1 := by simpa using hy
  have hprim : IsPrimitiveRoot y k := IsPrimitiveRoot.mk_of_lt y hk0 hy1
    fun l hl hlk => hyn l (hub.pow_ne_one_of_pos_of_lt hl.ne' hlk)
  refine ⟨T', hT', fun z hz => ?_⟩
  haveI : NeZero k := ⟨hk0.ne'⟩
  obtain ⟨i, -, rfl⟩ := hprim.eq_pow_of_pow_eq_one hz
  exact pow_mem hyT i

end GlobalTheory.KummerUnram

namespace GlobalTheory


open KummerUnram in
theorem exists_unramSub_of_pow_eq_units : ∀ (F : Type) [Field F] [IsAlgClosed F] (T : Subring F) [IsDiscreteValuationRing T] (k : ℕ), IsUnit (k : T) → ∀ U : Set Tˣ, U.Finite → ∃ T' : Subring F, GlobalTheory.UnramSub T.subtype T' ∧ ∀ x : F, (∃ u ∈ U, x ^ k = ((u : T) : F)) → x ∈ T' := by
  intro F _ _ T _ k hk U hU
  obtain ⟨T₁, h₁, hroots⟩ := exists_rootsOfUnity T hk
  suffices key : ∃ T' : Subring F, UnramSub T.subtype T' ∧ T₁ ≤ T' ∧
      ∀ x : F, (∃ u ∈ U, x ^ k = ((u : T) : F)) → x ∈ T' by
    obtain ⟨T', h, -, h'⟩ := key
    exact ⟨T', h, h'⟩
  induction U, hU using Set.Finite.induction_on with
  | empty => exact ⟨T₁, h₁, le_rfl, by simp⟩
  | @insert a s _ _ ih =>
    obtain ⟨T', hT', hle, hmem⟩ := ih
    haveI := hT'.isDVR
    have hTT' : T ≤ T' := fun z hz => hT'.mem ⟨z, hz⟩
    let ι : T →+* T' := Subring.inclusion hTT'
    have hk' : IsUnit (k : T') := by simpa [ι] using hk.map ι
    let a' : T'ˣ := Units.map ι.toMonoidHom a
    have hk0 : k ≠ 0 := by rintro rfl; exact not_isUnit_zero (M₀ := T) (by simpa using hk)
    obtain ⟨ub, hub⟩ := IsAlgClosed.exists_pow_nat_eq
      (algebraMap (ResidueField T') (AlgebraicClosure (ResidueField T')) (residue T' a'))
      (Nat.pos_of_ne_zero hk0)
    obtain ⟨T'', hT'', y, hyT, hy, -⟩ := exists_root_step T' hk' a' ub hub
    have hy' : y ^ k = ((a : T) : F) := by simpa [a', ι] using hy
    have ha0 : ((a : T) : F) ≠ 0 := fun h => a.ne_zero (Subtype.ext h)
    have hy0 : y ≠ 0 := by rintro rfl; exact ha0 (by rw [← hy', zero_pow hk0])
    have hle' : T' ≤ T'' := UnramSub.le hT''
    refine ⟨T'', hT'.trans hT'', hle.trans hle', fun x ⟨u, hu, hx⟩ => ?_⟩
    rcases Set.mem_insert_iff.1 hu with rfl | hu
    · have hz : (x / y) ^ k = 1 := by rw [div_pow, hx, hy', div_self ha0]
      have : x = (x / y) * y := by field_simp
      rw [this]
      exact mul_mem (hle' (hle (hroots _ hz))) hyT
    · exact hle' (hmem x ⟨u, hu, hx⟩)

end GlobalTheory
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.EtaleKlt

theorem formallyEtale_of_isIso {R S : CommRingCat.{0}} (e : R ⟶ S) [IsIso e] :
    e.hom.FormallyEtale := by
  letI := e.hom.toAlgebra
  let E : R ≃ₐ[R] S := { (asIso e).commRingCatIsoToRingEquiv with commutes' := fun _ => rfl }
  show Algebra.FormallyEtale R S
  exact Algebra.FormallyEtale.of_equiv E

theorem genericPoint_mem_of_nonempty {X : Scheme.{0}} [IsIntegral X] (U : X.Opens)
    (hU : (U : Set X).Nonempty) : genericPoint X ∈ U :=
  ((genericPoint_spec X).mem_open_set_iff U.isOpen).2 (by simpa using hU)

theorem map_genericPoint {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y] (f : X ⟶ Y)
    [IsDominant f] : f (genericPoint X) = genericPoint Y := by
  have := (genericPoint_spec X).image f.continuous
  rw [Set.image_univ, f.denseRange.closure_range] at this
  exact this.eq (genericPoint_spec Y)

theorem formallyEtale_functionFieldMap {M W : Scheme.{0}} [IsIntegral M] [IsIntegral W]
    (f : M ⟶ W) [IsDominant f] (U : M.Opens) (hf : Etale (U.ι ≫ f))
    (hU : (U : Set M).Nonempty) : (functionFieldMap f).FormallyEtale := by
  have hξ := genericPoint_mem_of_nonempty U hU
  let u : (U : Scheme.{0}) := ⟨genericPoint M, hξ⟩
  have h1 : ((U.ι ≫ f).stalkMap u).hom.FormallyEtale := by
    have hu := FormallyUnramified.stalkMap (U.ι ≫ f) u
    have hs : ((U.ι ≫ f).stalkMap u).hom.FormallySmooth :=
      Scheme.Hom.mem_smoothLocus.mp ((U.ι ≫ f).smoothLocus_eq_top.ge (Set.mem_univ u))
    algebraize [((U.ι ≫ f).stalkMap u).hom]
    exact Algebra.FormallyEtale.iff_formallyUnramified_and_formallySmooth.mpr ⟨hu, hs⟩
  rw [Scheme.Hom.stalkMap_comp] at h1
  have h2 : (f.stalkMap (genericPoint M)).hom.FormallyEtale := by
    have e : f.stalkMap (genericPoint M) =
        (f.stalkMap (U.ι u) ≫ U.ι.stalkMap u) ≫ inv (U.ι.stalkMap u) := by simp; rfl
    rw [e]
    exact RingHom.FormallyEtale.comp h1 (formallyEtale_of_isIso _)
  have hiso : ∀ {x : W} (h : x ⤳ genericPoint W), x = genericPoint W →
      IsIso (W.presheaf.stalkSpecializes h) := by
    rintro x h rfl
    rw [TopCat.Presheaf.stalkSpecializes_refl]
    infer_instance
  have key : ∀ h : f (genericPoint M) ⤳ genericPoint W,
      (W.presheaf.stalkSpecializes h ≫ f.stalkMap (genericPoint M)).hom.FormallyEtale := by
    intro h
    haveI := hiso h (map_genericPoint f)
    exact RingHom.FormallyEtale.comp (formallyEtale_of_isIso _) h2
  exact key _

theorem injective_of_isBaseChange_field {A B M N : Type*} [Field A] [CommRing B] [Nontrivial B]
    [Algebra A B] [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N] [Module B N]
    [IsScalarTower A B N] {φ : M →ₗ[A] N} (hφ : IsBaseChange B φ) : Function.Injective φ := by
  have e : (φ : M → N) = hφ.equiv ∘ ((Algebra.linearMap A B).rTensor M) ∘
      (TensorProduct.lid A M).symm := by
    funext m
    simp [hφ.equiv_tmul]
  rw [e]
  refine hφ.equiv.injective.comp ((Module.Flat.rTensor_preserves_injective_linearMap _
    (algebraMap A B).injective).comp (TensorProduct.lid A M).symm.injective)

theorem ratPull_ne_zero : ∀ (M W : Scheme.{0}) [IsIntegral M] [IsIntegral W] [IsLocallyNoetherian M]
    [IsLocallyNoetherian W] (p : W ⟶ Sp ℂ) (f : M ⟶ W) [IsDominant f] (n : ℕ)
    [SmoothOfRelativeDimension n p] [SmoothOfRelativeDimension n (f ≫ p)] (U : M.Opens),
    Etale (U.ι ≫ f) → (U : Set M).Nonempty → ∀ η : RatForms p n, η ≠ 0 →
      GlobalTheory.EtaleKlt.ratPull p f n η ≠ 0 := by
  intro M W _ _ _ _ p f _ n _ _ U hf hU η hη h0
  have hE := formallyEtale_functionFieldMap f U hf hU
  letI := (Cartier.constFn p).toAlgebra
  letI := (Cartier.constFn (f ≫ p)).toAlgebra
  letI := (functionFieldMap f).toAlgebra
  haveI : IsScalarTower ℂ W.functionField M.functionField :=
    IsScalarTower.of_algebraMap_eq' (functionFieldMap_comp_constFn p f).symm
  haveI : Algebra.FormallyEtale W.functionField M.functionField := hE
  have hb := isBaseChange_exteriorPower
    (KaehlerDifferential.isBaseChange_of_formallyEtale ℂ W.functionField M.functionField) n
  exact hη (injective_of_isBaseChange_field hb (h0.trans (map_zero _).symm))

end GlobalTheory.EtaleKlt
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

section Val
variable {F : Type} [Field F] {X : Scheme.{0}}

theorem valF_eq_hom (x : Sp F ⟶ X) {U : X.Opens} (h : ⊤ ≤ x ⁻¹ᵁ U) (f : Γ(X, U)) :
    valF x U f = ((Scheme.ΓSpecIso (CommRingCat.of F)).hom.hom.comp (x.appLE U ⊤ h).hom) f := by
  unfold valF
  rw [dite_eq_left h]
  rfl

theorem valF_zpow (x : Sp F ⟶ X) {U : X.Opens} (h : ⊤ ≤ x ⁻¹ᵁ U) (u : Γ(X, U)ˣ) (n : ℤ) :
    valF x U (u ^ n).val = valF x U u.val ^ n := by
  rw [valF_eq_hom x h, valF_eq_hom x h]
  have e := congrArg Units.val
    (map_zpow (Units.map ((Scheme.ΓSpecIso (CommRingCat.of F)).hom.hom.comp (x.appLE U ⊤ h).hom).toMonoidHom) u n)
  rw [Units.val_zpow_eq_zpow_val] at e
  exact e

theorem valF_prod {K : Type} [Fintype K] (x : Sp F ⟶ X) {U : X.Opens} (h : ⊤ ≤ x ⁻¹ᵁ U) (u : K → Γ(X, U)ˣ) :
    valF x U (∏ k, u k).val = ∏ k, valF x U (u k).val := by
  simp only [valF_eq_hom x h, Units.coe_prod, map_prod]

end Val

theorem cubF_mul_prod_fr {B : NumB ℂ} {g : ℕ} (d : AB B g) (x y z : Fin g → ℂ) :
    cubF d x y z * ∏ I : thK, ((d.fr (wI x y z I) : ℂˣ) : ℂ) ^ thε I = (B.θ (d.ex x) (d.ex y) (d.ex z) : ℂ) := by
  have p := GlobalTheory.FrameValue.prod_thK (fun s : Finset (Fin 3) => ((d.fr (∑ a ∈ s, ![x, y, z] a) : ℂˣ) : ℂ))
  simp only [GlobalTheory.FrameValue.sum_three, Finset.sum_singleton, Finset.sum_empty, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, d.fr_zero, Units.val_one] at p
  simp only [wI]
  rw [p, cubF, inv_one, _root_.mul_one]
  have h1 := (d.fr (x + y + z)).ne_zero
  have h2 := (d.fr (x + y)).ne_zero
  have h3 := (d.fr (x + z)).ne_zero
  have h4 := (d.fr (y + z)).ne_zero
  have h5 := (d.fr x).ne_zero
  have h6 := (d.fr y).ne_zero
  have h7 := (d.fr z).ne_zero
  field_simp

theorem cubF_mul_prod_frG {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} [Algebra (FractionRing R) ℂ] {N : NumD ℂ}
    {g : ℕ} (ν : NumOf D ℂ N) (d : AB N.toNumB g) (geo : Geo ν d) (x y z : Fin g → ℂ) (j : thK → D.P.L.ι)
    (hj : ⊤ ≤ pt3 ν d x y z ⁻¹ᵁ cubW D j) :
    cubF d x y z * ∏ I : thK, geo.frG (j I) (wI x y z I) ^ thε I =
      valF (pt3 ν d x y z) (cubW D j) (D.cub.t.s j).val := by
  set r := pt3 ν d x y z with hr
  set φ := thφ D.P.A (x3 D.P.A) with hφ
  set J' : thK → D.P.L.ι := fun I => ν.J (r ≫ φ I) with hJ'
  have hθ : (N.θ (d.ex x) (d.ex y) (d.ex z) : ℂ) = valF r (cubW D J') (D.cub.t.s J').val := ν.θ_eq _ _ _
  have hgood : ⊤ ≤ r ⁻¹ᵁ cubW D J' := fun p _ => Set.mem_iInter.2 fun I => ν.good (r ≫ φ I) (x := p) trivial
  have hboth := GlobalTheory.ZH.TorsFrame.le_preimage_inf r hgood hj
  have hg := D.cub.isGen J' j
  have e2 : valF r (cubW D J') (D.cub.t.s J').val =
      valF r (cubW D J' ⊓ cubW D j) ((Theta D.P.A D.P.L).g J' j).val * valF r (cubW D j) (D.cub.t.s j).val :=
    (GlobalTheory.ZH.TorsFrame.valF_res r (inf_le_left : cubW D J' ⊓ cubW D j ≤ cubW D J') hboth (D.cub.t.s J')).symm.trans
      ((congrArg (fun u => valF r (cubW D J' ⊓ cubW D j) (Units.val u)) hg).trans
        ((GlobalTheory.ZH.TorsFrame.valF_mul r hboth _ _).trans
          (congrArg (_ * ·) (GlobalTheory.ZH.TorsFrame.valF_res r inf_le_right hboth _))))
  have e3 : valF r (cubW D J' ⊓ cubW D j) ((Theta D.P.A D.P.L).g J' j).val =
      ∏ I : thK, valF (r ≫ φ I) (D.P.L.U (J' I) ⊓ D.P.L.U (j I)) (D.P.L.g (J' I) (j I)).val ^ thε I := by
    refine (valF_prod r hboth _).trans (Finset.prod_congr rfl fun I _ => ?_)
    refine (valF_zpow r hboth _ _).trans ?_
    congr 1
    exact (GlobalTheory.ZH.TorsFrame.valF_res r _ hboth _).trans (GlobalTheory.ZH.TorsFrame.valF_pullU r (φ I) (D.P.L.U (J' I) ⊓ D.P.L.U (j I)) (D.P.L.g (J' I) (j I)))
  have hc : ∀ I : thK, valF (r ≫ φ I) (D.P.L.U (J' I) ⊓ D.P.L.U (j I)) (D.P.L.g (J' I) (j I)).val *
      geo.frG (j I) (wI x y z I) = d.fr (wI x y z I) * ν.rg := by
    intro I
    have hin : ⊤ ≤ (r ≫ φ I) ⁻¹ᵁ (D.P.L.U (ν.J (r ≫ φ I)) ⊓ D.P.L.U (j I)) := fun p _ =>
      ⟨ν.good (r ≫ φ I) (x := p) trivial, Set.mem_iInter.1 (hj (x := p) trivial) I⟩
    have hp : r ≫ φ I = (ν.eA (d.ex (wI x y z I))).left := complexCubeAbelianPoint_thetaFace_eq_partialSum ν d x y z I
    show valF (r ≫ φ I) (D.P.L.U (ν.J (r ≫ φ I)) ⊓ D.P.L.U (j I)) (D.P.L.g (ν.J (r ≫ φ I)) (j I)).val *
      geo.frG (j I) (wI x y z I) = d.fr (wI x y z I) * ν.rg
    rw [hp] at hin ⊢
    rw [geo.fr_eq]
    exact (geo.fr_compat _ _ _ hin).symm
  have hrg : ν.rg ≠ 0 := GlobalTheory.Ex.Arch.AbVal.rg_ne_zero ν
  set a : thK → ℂ := fun I => valF (r ≫ φ I) (D.P.L.U (J' I) ⊓ D.P.L.U (j I)) (D.P.L.g (J' I) (j I)).val with ha_def
  set fG : thK → ℂ := fun I => geo.frG (j I) (wI x y z I) with hfG
  set V := valF r (cubW D j) (D.cub.t.s j).val with hV
  set θ : ℂ := (N.θ (d.ex x) (d.ex y) (d.ex z) : ℂ) with hθd
  have hθ' : θ = (∏ I : thK, a I ^ thε I) * V := by rw [hθ, e2, e3]
  have ha : ∀ I, a I ≠ 0 := fun I h0 => by
    have := hc I
    rw [show valF (r ≫ φ I) (D.P.L.U (J' I) ⊓ D.P.L.U (j I)) (D.P.L.g (J' I) (j I)).val = a I from rfl, h0,
      zero_mul] at this
    exact mul_ne_zero (Units.ne_zero _) hrg this.symm
  have hPa : (∏ I : thK, a I ^ thε I) ≠ 0 := Finset.prod_ne_zero_iff.2 fun I _ => zpow_ne_zero _ (ha I)
  have hrg1 : (∏ _I : thK, ν.rg ^ thε _I) = 1 := by
    have p := GlobalTheory.FrameValue.prod_thK (fun _ : Finset (Fin 3) => ν.rg)
    refine p.trans ?_
    field_simp
  have hP : (∏ I : thK, a I ^ thε I) * (∏ I : thK, fG I ^ thε I) =
      ∏ I : thK, ((d.fr (wI x y z I) : ℂˣ) : ℂ) ^ thε I := by
    rw [← Finset.prod_mul_distrib]
    have : ∀ I : thK, a I ^ thε I * fG I ^ thε I = ((d.fr (wI x y z I) : ℂˣ) : ℂ) ^ thε I * ν.rg ^ thε I :=
      fun I => by rw [← mul_zpow, ← mul_zpow]; exact congrArg (· ^ thε I) (hc I)
    rw [Finset.prod_congr rfl fun I _ => this I, Finset.prod_mul_distrib, hrg1, _root_.mul_one]
  have hcub := cubF_mul_prod_fr d x y z
  show cubF d x y z * ∏ I : thK, fG I ^ thε I = V
  refine mul_left_cancel₀ hPa ?_
  linear_combination cubF d x y z * hP + hcub + hθ'

end GlobalTheory.MBLow.Cl.CubHol

end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.TanGauge

noncomputable section
namespace GlobalTheory.MBLow.TanGauge

theorem valR_linComb_g_factor {X Y : Scheme.{0}} (L : LB X) {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ)
    {A : Type} [CommRing A] (y : Sp A ⟶ Y) (j j' : K → L.ι)
    (hh : ⊤ ≤ y ⁻¹ᵁ (LB.wchart L φ j ⊓ LB.wchart L φ j')) (k : K) :
    valR y (LB.wchart L φ j ⊓ LB.wchart L φ j')
      ((res (le_inf (inf_le_left.trans (LB.wchart_le L φ j k))
      (inf_le_right.trans (LB.wchart_le L φ j' k)) :
        LB.wchart L φ j ⊓ LB.wchart L φ j' ≤ φ k ⁻¹ᵁ (L.U (j k) ⊓ L.U (j' k)))
      (pullU (φ k) _ (L.g (j k) (j' k)))) ^ (ε k)).val = trV L (y ≫ φ k) (j k) (j' k) (ε k) := by
  have h0 : LB.wchart L φ j ⊓ LB.wchart L φ j' ≤ φ k ⁻¹ᵁ (L.U (j k) ⊓ L.U (j' k)) :=
    le_inf (inf_le_left.trans (LB.wchart_le L φ j k)) (inf_le_right.trans (LB.wchart_le L φ j' k))
  have key : (res h0 (pullU (φ k) (L.U (j k) ⊓ L.U (j' k)) (L.g (j k) (j' k)))) ^ (ε k) =
      res h0 (pullU (φ k) (L.U (j k) ⊓ L.U (j' k)) ((L.g (j k) (j' k)) ^ (ε k))) :=
    ((congrArg (res h0) (map_zpow (pullU (φ k) (L.U (j k) ⊓ L.U (j' k))) _ _)).trans
      (map_zpow (res h0) _ _)).symm
  refine (congrArg (fun u => valR y (LB.wchart L φ j ⊓ LB.wchart L φ j') (Units.val u)) key).trans ?_
  have e1 := GlobalTheory.ZH.CrdCalc.valR_res y h0 hh
      (((φ k).app (L.U (j k) ⊓ L.U (j' k))).hom ((L.g (j k) (j' k)) ^ (ε k)).val)
  refine Eq.trans ?_ (e1.trans ?_)
  · rfl
  · unfold trV
    exact GlobalTheory.ZH.EvCrd.valR_comp y (φ k) _ (hh.trans (y.preimage_mono h0)) _

theorem valR_gen_linComb : ∀ {X Y : Scheme.{0}} (L : LB X) {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ)
    (t : LB.Gen (LB.LinComb L φ ε)), t.IsGen → ∀ {A : Type} [CommRing A] (y : Sp A ⟶ Y) (j j' : K → L.ι),
    ⊤ ≤ y ⁻¹ᵁ LB.wchart L φ j → ⊤ ≤ y ⁻¹ᵁ LB.wchart L φ j' →
    valR y (LB.wchart L φ j) (t.s j).val =
      (∏ k, trV L (y ≫ φ k) (j k) (j' k) (ε k)) * valR y (LB.wchart L φ j') (t.s j').val := by
  intro X Y L K _ φ ε t ht A _ y j j' h h'
  have hh : ⊤ ≤ y ⁻¹ᵁ (LB.wchart L φ j ⊓ LB.wchart L φ j') := fun q hq => ⟨h hq, h' hq⟩
  have e : valR y (LB.wchart L φ j ⊓ LB.wchart L φ j')
      (res (inf_le_left : LB.wchart L φ j ⊓ LB.wchart L φ j' ≤ LB.wchart L φ j) (t.s j)).val =
      valR y (LB.wchart L φ j ⊓ LB.wchart L φ j')
      ((show Γ(Y, LB.wchart L φ j ⊓ LB.wchart L φ j')ˣ from (LB.LinComb L φ ε).g j j').val *
        (res (inf_le_right : LB.wchart L φ j ⊓ LB.wchart L φ j' ≤ LB.wchart L φ j') (t.s j')).val) :=
    congrArg (fun u => valR y (LB.wchart L φ j ⊓ LB.wchart L φ j') (Units.val u)) (ht j j')
  rw [GlobalTheory.ZH.CrdCalc.valR_mul y _ hh] at e
  have e1 := GlobalTheory.ZH.CrdCalc.valR_res y (inf_le_left : LB.wchart L φ j ⊓ LB.wchart L φ j' ≤ LB.wchart L φ j) hh (t.s j).val
  have e2 := GlobalTheory.ZH.CrdCalc.valR_res y (inf_le_right : LB.wchart L φ j ⊓ LB.wchart L φ j' ≤ LB.wchart L φ j') hh (t.s j').val
  have e3 : valR y (LB.wchart L φ j ⊓ LB.wchart L φ j') (show Γ(Y, LB.wchart L φ j ⊓ LB.wchart L φ j')ˣ from (LB.LinComb L φ ε).g j j').val =
      ∏ k, trV L (y ≫ φ k) (j k) (j' k) (ε k) := by
    change valR y (LB.wchart L φ j ⊓ LB.wchart L φ j') (Units.val (∏ k, _)) = _
    rw [Units.coe_prod, GlobalTheory.ZH.CrdCalc.valR_eq y _ hh, map_prod]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [← GlobalTheory.ZH.CrdCalc.valR_eq y _ hh]
    exact valR_linComb_g_factor L φ ε y j j' hh k
  rw [← e3]
  exact e1.symm.trans (e.trans (congrArg _ e2))

end GlobalTheory.MBLow.TanGauge
end
end
