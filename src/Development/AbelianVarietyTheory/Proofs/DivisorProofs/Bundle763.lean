module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle021
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle733
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StructureSheafCohomologyPullbackCompCupId
public import Development.AbelianVarietyTheory.Definitions.Divisors.ComparisonMemCechHodgeFiltration
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle002
public import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChosenInjectiveResolutionEtaleSheafSectionsExactStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle463
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle730
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle406
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle508
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle344
public import Development.AbelianVarietyTheory.Definitions.Divisors.EntireEqOfHalfPlane
public import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle005
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle721
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle726
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiLogarithmLevelOneDefectFrobeniusPow
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.TorsTransport
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle012

@[expose] public section

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CechPoset

namespace GlobalTheory.CechPoset

theorem trivCoord_restrict {X X' : Scheme.{0}} {R' : Type} [CommRing R'] (φ : X' ⟶ X) (s' : X' ⟶ Sp R')
    {V W : X'.Opens} (h : W ≤ V) (x : GlobalTheory.AbLaw.SecOnR s' ((LB.triv X).pull φ) V) :
    trivCoord φ s' W (GlobalTheory.AbLaw.SecOnR.restrict s' _ h x) = Sec.res s' h (trivCoord φ s' V x) := by
  simp only [trivCoord, LinearMap.coe_mk, AddHom.coe_mk, GlobalTheory.AbLaw.SecOnR.coord_restrict]
  change (X'.presheaf.map _ ≫ X'.presheaf.map _).hom _ = (X'.presheaf.map _ ≫ X'.presheaf.map _).hom _
  rw [← Functor.map_comp, ← Functor.map_comp]; rfl

theorem Φ_apply {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R'] {X X' : Scheme.{0}} {s : X ⟶ Sp R}
    {s' : X' ⟶ Sp R'} {φ : X' ⟶ X} (w : φ ≫ s = s' ≫ spMap (algebraMap R R')) {κ : Type} [LinearOrder κ]
    (D : κ → X.Opens) (hD' : ∀ I : Finset κ, I.Nonempty → IsAffineOpen (⨅ i ∈ I, φ ⁻¹ᵁ D i)) (q : ℕ)
    (x : R' ⊗[R] (GlobalTheory.AbLaw.cechLB s (LB.triv X) D).X q)
    (t : {s : Finset κ // s.card = q + 1}) :
    Φ w D hD' q x t = trivCoord φ s' (⨅ i ∈ t.1, φ ⁻¹ᵁ D i) (GlobalTheory.AbLaw.secTermBaseChange (LB.triv X) D w (q + 1) x t) :=
  rfl

theorem trivCoord_d {R' : Type} [CommRing R'] {X X' : Scheme.{0}} {s' : X' ⟶ Sp R'} (φ : X' ⟶ X) {κ : Type}
    [LinearOrder κ] (D : κ → X.Opens) (hD' : ∀ I : Finset κ, I.Nonempty → IsAffineOpen (⨅ i ∈ I, φ ⁻¹ᵁ D i))
    (p : ℕ) (y : GlobalTheory.Cube.Term (GlobalTheory.AbLaw.secCube s' ((LB.triv X).pull φ) fun i => φ ⁻¹ᵁ D i) (p + 1))
    (t : {s : Finset κ // s.card = p + 1 + 1}) :
    trivCoord φ s' (⨅ i ∈ t.1, φ ⁻¹ᵁ D i) (GlobalTheory.Cube.d _ (p + 1) y t) =
      δ (covF s' (fun i => φ ⁻¹ᵁ D i) hD') p (fun u => trivCoord φ s' (⨅ i ∈ u.1, φ ⁻¹ᵁ D i) (y u)) t := by
  refine (congrArg (trivCoord φ s' (⨅ i ∈ t.1, φ ⁻¹ᵁ D i)) (GlobalTheory.Cube.d_apply _ (p + 1) y t)).trans ?_
  refine ((map_sum (trivCoord φ s' (⨅ i ∈ t.1, φ ⁻¹ᵁ D i)) _ _)).trans ?_
  refine Eq.trans ?_ (δ_apply (covF s' (fun i => φ ⁻¹ᵁ D i) hD') p _ t).symm
  refine Finset.sum_congr rfl fun i _ => ?_
  refine (map_zsmul (trivCoord φ s' (⨅ i ∈ t.1, φ ⁻¹ᵁ D i)) _ _).trans ?_
  congr 1
  exact trivCoord_restrict φ s' _ _

theorem Φ_dB : ∀ {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R'] {X X' : Scheme.{0}} {s : X ⟶ Sp R} {s' : X' ⟶ Sp R'} {φ : X' ⟶ X} (w : φ ≫ s = s' ≫ spMap (algebraMap R R')) {κ : Type} [LinearOrder κ] (D : κ → X.Opens) (hD' : ∀ I : Finset κ, I.Nonempty → IsAffineOpen (⨅ i ∈ I, φ ⁻¹ᵁ D i)) (p : ℕ) (x : R' ⊗[R] (GlobalTheory.AbLaw.cechLB s (LB.triv X) D).X p), Φ w D hD' (p + 1) (dB (GlobalTheory.AbLaw.cechLB s (LB.triv X) D) R' p (p + 1) x) = δ _ p (Φ w D hD' p x) := by
  intro R R' _ _ _ X X' s s' φ w κ _ D hD' p x
  have e1 : dB (GlobalTheory.AbLaw.cechLB s (LB.triv X) D) R' p (p + 1) x =
      (GlobalTheory.Cube.d (GlobalTheory.AbLaw.secCube s (LB.triv X) D) (p + 1)).baseChange R' x := by
    simp only [dB, GlobalTheory.AbLaw.cechLB_d]; rfl
  have e2 := GlobalTheory.AbLaw.d_secTermBaseChange (LB.triv X) D w (p + 1) x
  funext t
  refine (Φ_apply w D hD' (p + 1) _ t).trans ?_
  refine (congrArg (fun z => trivCoord φ s' (⨅ i ∈ t.1, φ ⁻¹ᵁ D i)
    (GlobalTheory.AbLaw.secTermBaseChange (LB.triv X) D w (p + 1 + 1) z t)) e1).trans ?_
  refine (congrArg (fun z => trivCoord φ s' (⨅ i ∈ t.1, φ ⁻¹ᵁ D i) (z t)) e2.symm).trans ?_
  exact trivCoord_d φ D hD' p _ t

end GlobalTheory.CechPoset
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CechPoset

namespace GlobalTheory.CechPoset

theorem trivCoord_pull_comp {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] {g' : R →+* R'} {g'' : R →+* R''}
    {X X' X'' : Scheme.{0}} {s : X ⟶ Sp R} {s' : X' ⟶ Sp R'} {s'' : X'' ⟶ Sp R''} {φ : X' ⟶ X} {φ' : X'' ⟶ X}
    (w' : φ ≫ s = s' ≫ spMap g') (w'' : φ' ≫ s = s'' ≫ spMap g'') (ψ : X'' ⟶ X') (h : ψ ≫ φ = φ')
    (V : X.Opens) (V' : X'.Opens) (V'' : X''.Opens) (e' : V' ≤ φ ⁻¹ᵁ V) (e'' : V'' ≤ φ' ⁻¹ᵁ V) (e : V'' ≤ ψ ⁻¹ᵁ V')
    (x : GlobalTheory.AbLaw.SecOnR s (LB.triv X) V) :
    trivCoord φ' s'' V'' (GlobalTheory.AbLaw.SecOnR.pull (LB.triv X) w'' V V'' e'' x) =
      (ψ.appLE V' V'' e).hom (trivCoord φ s' V' (GlobalTheory.AbLaw.SecOnR.pull (LB.triv X) w' V V' e' x)) := by
  subst h
  have k : ∀ {Y : Scheme.{0}} {S : Type} [CommRing S] {g : R →+* S} (t : Y ⟶ Sp S) (π : Y ⟶ X)
      (w : π ≫ s = t ≫ spMap g) (O : Y.Opens) (eO : O ≤ π ⁻¹ᵁ V) (e2 : O ≤ π ⁻¹ᵁ (V ⊓ (LB.triv X).U PUnit.unit)),
      trivCoord π t O (GlobalTheory.AbLaw.SecOnR.pull (LB.triv X) w V O eO x) =
        (π.appLE _ O e2).hom (x.coord PUnit.unit) := by
    intro Y S _ g t π w O eO e2
    have := GlobalTheory.AbLaw.SecOn.coord_pullLE π eO ((GlobalTheory.AbLaw.SecOnR.of s (LB.triv X) V).symm x) (i0 π)
    refine (congrArg (Sec.res t (le_inf le_rfl (by rw [triv_pull_U]; exact le_top))) this).trans ?_
    exact GlobalTheory.LB.resG_appLE π _ _ _
  have e2 : V' ≤ φ ⁻¹ᵁ (V ⊓ (LB.triv X).U PUnit.unit) := fun y hy => ⟨e' hy, trivial⟩
  rw [k s' φ w' V' e' e2, k s'' (ψ ≫ φ) w'' V'' e'' (fun y hy => e2 (e hy))]
  exact (congrArg (fun q => q.hom (x.coord PUnit.unit)) (Scheme.Hom.appLE_comp_appLE ψ φ _ V' V'' e2 e)).symm

theorem Φ_ext_eq_pullCoef : ∀ {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] [Algebra R R'] [Algebra R R''] {X X' X'' : Scheme.{0}} {s : X ⟶ Sp R} {s' : X' ⟶ Sp R'} {s'' : X'' ⟶ Sp R''} {φ : X' ⟶ X} {φ' : X'' ⟶ X} (w' : φ ≫ s = s' ≫ spMap (algebraMap R R')) (w'' : φ' ≫ s = s'' ≫ spMap (algebraMap R R'')) (α : R' →ₐ[R] R'') (ψ : X'' ⟶ X') (wψ : ψ ≫ s' = s'' ≫ spMap (α : R' →+* R'')), ψ ≫ φ = φ' → ∀ {κ : Type} [LinearOrder κ] (D : κ → X.Opens) (hD' : ∀ I : Finset κ, I.Nonempty → IsAffineOpen (⨅ i ∈ I, φ ⁻¹ᵁ D i)) (hD'' : ∀ I : Finset κ, I.Nonempty → IsAffineOpen (⨅ i ∈ I, φ' ⁻¹ᵁ D i)) (hle : ∀ i, φ' ⁻¹ᵁ D i ≤ ψ ⁻¹ᵁ (φ ⁻¹ᵁ D i)) (p : ℕ) (z : R' ⊗[R] (GlobalTheory.AbLaw.cechLB s (LB.triv X) D).X p) (t : {s : Finset κ // s.card = p + 1}), Φ w'' D hD'' p (GlobalTheory.AbCoh.ext α _ z) t = (pullCoef wψ (fun i => φ ⁻¹ᵁ D i) hD' (fun i => φ' ⁻¹ᵁ D i) hD'' hle).α (ne t.1 (card_nonempty t)) (Φ w' D hD' p z t) := by
  intro R R' R'' _ _ _ _ _ X X' X'' s s' s'' φ φ' w' w'' α ψ wψ h κ _ D hD' hD'' hle p z t
  induction z using TensorProduct.induction_on with
  | zero =>
    rw [map_zero, map_zero, map_zero]
    exact (map_zero ((pullCoef wψ (fun i => φ ⁻¹ᵁ D i) hD' (fun i => φ' ⁻¹ᵁ D i) hD'' hle).α (ne t.1 (card_nonempty t)))).symm
  | add x y hx hy =>
    rw [map_add (f := _), map_add (f := _), map_add (f := _)]
    exact (congrArg₂ (· + ·) hx hy).trans (map_add ((pullCoef wψ (fun i => φ ⁻¹ᵁ D i) hD' (fun i => φ' ⁻¹ᵁ D i) hD'' hle).α (ne t.1 (card_nonempty t))) _ _).symm
  | tmul r x =>
    have a1 : Φ w'' D hD'' p (GlobalTheory.AbCoh.ext α _ (r ⊗ₜ x)) t = trivCoord φ' s'' _ (α r • GlobalTheory.AbLaw.secCubePull (LB.triv X) D w'' t.1 (x t)) := rfl
    have a2 : Φ w' D hD' p (r ⊗ₜ x) t = trivCoord φ s' _ (r • GlobalTheory.AbLaw.secCubePull (LB.triv X) D w' t.1 (x t)) := rfl
    refine a1.trans (Eq.trans ?_ (congrArg ((pullCoef wψ (fun i => φ ⁻¹ᵁ D i) hD' (fun i => φ' ⁻¹ᵁ D i) hD'' hle).α (ne t.1 (card_nonempty t))) a2).symm)
    refine ((trivCoord φ' s'' _).map_smul _ _).trans ?_
    refine Eq.trans ?_ (congrArg ((pullCoef wψ (fun i => φ ⁻¹ᵁ D i) hD' (fun i => φ' ⁻¹ᵁ D i) hD'' hle).α (ne t.1 (card_nonempty t))) ((trivCoord φ s' _).map_smul _ _)).symm
    refine Eq.trans ?_ ((pullCoef wψ (fun i => φ ⁻¹ᵁ D i) hD' (fun i => φ' ⁻¹ᵁ D i) hD'' hle).smul (ne t.1 (card_nonempty t)) r _).symm
    exact congrArg (α r • ·) (trivCoord_pull_comp w' w'' ψ h _ _ _ _ _ (pr _ hD' _ hD'' hle (ne t.1 (card_nonempty t)).unop).2 (x t))

end GlobalTheory.CechPoset
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh

namespace GlobalTheory.CechPoset

theorem restrict_pull2_pullHO2 {R' R'' : Type} [CommRing R'] [CommRing R''] {X' X'' : Scheme.{0}}
    {s' : X' ⟶ Sp R'} {s'' : X'' ⟶ Sp R''} {σ : R' →+* R''} {ψ : X'' ⟶ X'}
    (w : ψ ≫ s' = s'' ≫ spMap σ) {κ : Type} [LinearOrder κ] (D' : κ → X'.Opens)
    (hD' : ∀ I : Finset κ, I.Nonempty → IsAffineOpen (⨅ i ∈ I, D' i)) (D'' : κ → X''.Opens)
    (hD'' : ∀ I : Finset κ, I.Nonempty → IsAffineOpen (⨅ i ∈ I, D'' i))
    (hle : ∀ i, D'' i ≤ ψ ⁻¹ᵁ D' i) (y : HO2 s') :
    (CoefMap.restrict (OAff s'') (cov_mono D'' hD'').functor.op).pull2 (pullHO2 w y) =
      (pullCoef w D' hD' D'' hD'' hle).pull2
        ((CoefMap.restrict (OAff s') (cov_mono D' hD').functor.op).pull2 y) := by
  have hm : Monotone (pr D' hD' D'' hD'' hle) := fun I J h =>
    Subtype.mk_le_mk.2 (Prod.mk_le_mk.2 ⟨cov_mono D'' hD'' h, cov_mono D' hD' h⟩)
  have h1 : (pairRes ψ s'').pull2 (pullHO2 w y) = (pairPull w).pull2 y :=
    (LinearEquiv.ofBijective (pairRes ψ s'').pull2 (pairRes_pull2_bijective ψ s'')).apply_symm_apply _
  have h2 := congrArg (CoefMap.restrict (OPair ψ s'') hm.functor.op).pull2 h1
  generalize pullHO2 w y = z at h2 ⊢
  obtain ⟨z, rfl⟩ := CatCoh.H2.mk_surjective _ z
  obtain ⟨y, rfl⟩ := CatCoh.H2.mk_surjective _ y
  exact h2

end GlobalTheory.CechPoset
end
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.structureSheafCohomology_pullback_comp_cup_id : (∀ (R R' : Type) [CommRing R] [CommRing R'] (X X' : Scheme.{0}) (s : X ⟶ Sp R) (s' : X' ⟶ Sp R') (σ : R →+* R') (φ : X' ⟶ X) (h : φ ≫ s = s' ≫ spMap σ) (R'' : Type) [CommRing R''] (X'' : Scheme.{0}) (s'' : X'' ⟶ Sp R'') (τ : R' →+* R'') (ψ : X'' ⟶ X') (h' : ψ ≫ s' = s'' ≫ spMap τ) (ρ : R →+* R'') (χ : X'' ⟶ X) (h'' : χ ≫ s = s'' ≫ spMap ρ), χ = ψ ≫ φ → (∀ r, ρ r = τ (σ r)) → (∀ a, pullHO1 h' (pullHO1 h a) = pullHO1 h'' a) ∧ (∀ a, pullHO2 h' (pullHO2 h a) = pullHO2 h'' a) ∧ (∀ a, GlobalTheory.CechDR.pullForm h' (GlobalTheory.CechDR.pullForm h a) = GlobalTheory.CechDR.pullForm h'' a) ∧ (∀ a, pullHH1 h' (pullHH1 h a) = pullHH1 h'' a) ∧ ∀ a, pullHH2 h' (pullHH2 h a) = pullHH2 h'' a) ∧ (∀ (R R' : Type) [CommRing R] [CommRing R'] (X X' : Scheme.{0}) (s : X ⟶ Sp R) (s' : X' ⟶ Sp R') (σ : R →+* R') (φ : X' ⟶ X) (h : φ ≫ s = s' ≫ spMap σ), (∀ a b, pullHO2 h (cup _ a b) = cup _ (pullHO1 h a) (pullHO1 h b)) ∧ (∀ a b, pullHH2 h (cupHH s a b) = cupHH s' (pullHH1 h a) (pullHH1 h b)) ∧ ∀ a, toHO1 s' (pullHH1 h a) = pullHO1 h (toHO1 s a)) ∧ ∀ (R : Type) [CommRing R] (A : Over (Sp R)), (∀ a, pO1 (𝟙 A) a = a) ∧ (∀ a, structureSheafH2Pullback (𝟙 A) a = a) ∧ (∀ a, pF (𝟙 A) a = a) ∧ (∀ a, deRhamH1Pullback (𝟙 A) a = a) ∧ ∀ a, deRhamH2Pullback (𝟙 A) a = a := by
  first | exact @GlobalTheory.AbCoh.pull_comp_cup_id | exact GlobalTheory.AbCoh.pull_comp_cup_id | (intros; apply GlobalTheory.AbCoh.pull_comp_cup_id <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CechFin

open GlobalTheory.CatCoh GlobalTheory.CechDR

variable {Z : Scheme.{0}} {J : Type} (W : J → Z.Opens)

def IsCoc (c : ∀ i i' : J, Γ(Z, W i ⊓ W i')) : Prop :=
  ∀ i i' i'', resG Z (inf_le_left : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i') (c i i') +
      resG Z (le_inf (inf_le_left.trans inf_le_right) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i' ⊓ W i'')
        (c i' i'') =
    resG Z (le_inf (inf_le_left.trans inf_le_left) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i'') (c i i'')

def CechFG (R : Type) [CommRing R] (act : ∀ i i' : J, R →+* Γ(Z, W i ⊓ W i')) : Prop :=
  ∃ (N : ℕ) (e : Fin N → ∀ i i' : J, Γ(Z, W i ⊓ W i')), (∀ k, IsCoc W (e k)) ∧
    ∀ c : ∀ i i' : J, Γ(Z, W i ⊓ W i'), IsCoc W c → ∃ (r : Fin N → R) (h : ∀ i : J, Γ(Z, W i)),
      ∀ i i', c i i' = resG Z inf_le_left (h i) - resG Z inf_le_right (h i') + ∑ k, act i i' (r k) * e k i i'

variable {R : Type} [CommRing R] (s : Z ⟶ Sp R)

def fv (f : C1 (OAff s)) {A B : Z.affineOpens} (h : B.1 ≤ A.1) : Γ(Z, B.1) :=
  f (Opposite.op A) (Opposite.op B) (homOfLE h).op

def gv (g : C0 (OAff s)) (A : Z.affineOpens) : Γ(Z, A.1) := g (Opposite.op A)

theorem fv_d0 (g : C0 (OAff s)) {A B : Z.affineOpens} (h : B.1 ≤ A.1) :
    fv s (d0 (OAff s) g) h = gv s g B - resG Z h (gv s g A) := rfl

theorem fv_add (f f' : C1 (OAff s)) {A B : Z.affineOpens} (h : B.1 ≤ A.1) :
    fv s (f + f') h = fv s f h + fv s f' h := rfl

theorem fv_smul (r : R) (f : C1 (OAff s)) {A B : Z.affineOpens} (h : B.1 ≤ A.1) :
    fv s (r • f) h = (secMap s B.1).hom r * fv s f h := rfl

theorem res_val (f : Z1 (OAff s)) {A B C : Z.affineOpens} (hBA : B.1 ≤ A.1) (hCB : C.1 ≤ B.1) :
    resG Z hCB (fv s f.1 hBA) = fv s f.1 (hCB.trans hBA) - fv s f.1 (A := B) hCB :=
  eq_sub_of_add_eq (f.2 (homOfLE hBA).op (homOfLE hCB).op).symm

variable (hW : ∀ i, IsAffineOpen (W i)) (hW2 : ∀ i i', IsAffineOpen (W i ⊓ W i'))

def rho (f : C1 (OAff s)) (i i' : J) : Γ(Z, W i ⊓ W i') :=
  fv s f (A := ⟨W i, hW i⟩) (B := ⟨W i ⊓ W i', hW2 i i'⟩) inf_le_left -
    fv s f (A := ⟨W i', hW i'⟩) (B := ⟨W i ⊓ W i', hW2 i i'⟩) inf_le_right

theorem rho_isCoc (hW3 : ∀ i i' i'', IsAffineOpen (W i ⊓ W i' ⊓ W i'')) (f : Z1 (OAff s)) :
    IsCoc W (rho W s hW hW2 f.1) := by
  intro i i' i''
  let T : Z.affineOpens := ⟨W i ⊓ W i' ⊓ W i'', hW3 i i' i''⟩
  have h1 := res_val s f (A := ⟨W i, hW i⟩) (B := ⟨W i ⊓ W i', hW2 i i'⟩) (C := T) inf_le_left inf_le_left
  have h2 := res_val s f (A := ⟨W i', hW i'⟩) (B := ⟨W i ⊓ W i', hW2 i i'⟩) (C := T) inf_le_right inf_le_left
  have h3 := res_val s f (A := ⟨W i', hW i'⟩) (B := ⟨W i' ⊓ W i'', hW2 i' i''⟩) (C := T) inf_le_left
    (le_inf (inf_le_left.trans inf_le_right) inf_le_right)
  have h4 := res_val s f (A := ⟨W i'', hW i''⟩) (B := ⟨W i' ⊓ W i'', hW2 i' i''⟩) (C := T) inf_le_right
    (le_inf (inf_le_left.trans inf_le_right) inf_le_right)
  have h5 := res_val s f (A := ⟨W i, hW i⟩) (B := ⟨W i ⊓ W i'', hW2 i i''⟩) (C := T) inf_le_left
    (le_inf (inf_le_left.trans inf_le_left) inf_le_right)
  have h6 := res_val s f (A := ⟨W i'', hW i''⟩) (B := ⟨W i ⊓ W i'', hW2 i i''⟩) (C := T) inf_le_right
    (le_inf (inf_le_left.trans inf_le_left) inf_le_right)
  simp only [rho, map_sub]
  rw [h1, h2, h3, h4, h5, h6]
  ring

theorem rho_add (f f' : C1 (OAff s)) (i i' : J) :
    rho W s hW hW2 (f + f') i i' = rho W s hW hW2 f i i' + rho W s hW hW2 f' i i' := by
  simp only [rho, fv_add]
  ring

theorem rho_smul (r : R) (f : C1 (OAff s)) (i i' : J) :
    rho W s hW hW2 (r • f) i i' = (secMap s (W i ⊓ W i')).hom r * rho W s hW hW2 f i i' := by
  simp only [rho, fv_smul]
  ring

theorem rho_zero (i i' : J) : rho W s hW hW2 0 i i' = 0 := sub_self (0 : Γ(Z, W i ⊓ W i'))

theorem rho_sum {N : ℕ} (r : Fin N → R) (f : Fin N → C1 (OAff s)) (i i' : J) :
    rho W s hW hW2 (∑ k, r k • f k) i i' = ∑ k, (secMap s (W i ⊓ W i')).hom (r k) * rho W s hW hW2 (f k) i i' := by
  induction N with
  | zero => simp only [Finset.univ_eq_empty, Finset.sum_empty]; exact rho_zero W s hW hW2 i i'
  | succ n ih =>
    rw [Fin.sum_univ_succ, Fin.sum_univ_succ, rho_add, rho_smul, ih]

theorem rho_d0 (g : C0 (OAff s)) (i i' : J) :
    rho W s hW hW2 (d0 (OAff s) g) i i' =
      resG Z inf_le_left (-gv s g ⟨W i, hW i⟩) - resG Z inf_le_right (-gv s g ⟨W i', hW i'⟩) := by
  simp only [rho, fv_d0, map_neg]
  ring

end GlobalTheory.CechFin
end
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem a6supp : DivisorSupportCondition := by
  intro q _ U V E f g hc n m i j a b ha hb
  exact GlobalTheory.T.cupProduct_eq_zero_of_vanishing_on_cover (ZMod q) (twPair q i j) ((GlobalTheory.T.chosenInjectiveResolution_etaleSheaf_properties (ZMod q) (tw q i)).2.1)
    ((GlobalTheory.T.chosenInjectiveResolution_etaleSheaf_properties (ZMod q) (tw q j)).2.1) f g hc rfl a b ha hb

end GlobalTheory.EtC
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem secMap_secRes_comm {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U)
    (x : Sec F U) : Sec.map φ (Sec.res g x) = Sec.res g (Sec.map φ x) := by
  change (φ.hom.app (op V)).hom ((F.obj.map g.op).hom x) = (G.obj.map g.op).hom ((φ.hom.app (op U)).hom x)
  rw [← ModuleCat.comp_apply, ← ModuleCat.comp_apply, φ.hom.naturality]

theorem secRes_secRes {R : Type} [CommRing R] {F : Shv R} {W V U : Scheme.{0}} (k : W ⟶ V) (g : V ⟶ U)
    (x : Sec F U) : Sec.res k (Sec.res g x) = Sec.res (k ≫ g) x := by
  change (F.obj.map k.op).hom ((F.obj.map g.op).hom x) = (F.obj.map (k ≫ g).op).hom x
  rw [op_comp, Functor.map_comp, ModuleCat.comp_apply]

theorem classes_die_on_etale_cover : A5 := by
  intro R _ X F n hn x
  obtain ⟨α, rfl⟩ := x.mk_surjective
  have hsch := GlobalTheory.T.cocycle_ev_d_eq_zero_and_mk_eq_zero_iff R X (res R F) (n - 1) n (n + 1) (by omega) rfl
  have hres := GlobalTheory.T.chosenInjectiveResolutionEtaleSheaf_sections_exactness R F X
  set z := ev α.1 0 n (by simp) X (𝟙 X) with hz
  have hdz : Sec.map ((res R F).d n (n + 1)) z = 0 := (hsch.2 α).1
  have hloc := hres.2.2.1 (n - 1) n (n + 1) hn (by omega) z rfl hdz
  rw [loc_iff_etale_affine_points] at hloc
  swap
  · rintro V W g k ⟨y, hy⟩
    refine ⟨Sec.res k y, ?_⟩
    rw [secMap_secRes_comm, hy, secRes_secRes]
  choose V g _ hg hmem y hy using hloc
  let f : (∐ V) ⟶ X := Sigma.desc g
  have hιf : ∀ i, Sigma.ι V i ≫ f = g i := fun i => Sigma.ι_desc g i
  refine ⟨∐ V, f, ?_, ?_, ?_⟩
  · have : IsZariskiLocalAtSource @Etale := HasRingHomProperty.instIsZariskiLocalAtSource
    exact IsZariskiLocalAtSource.sigmaDesc (P := @Etale) hg
  · refine ⟨fun p => ?_⟩
    obtain ⟨q, hq⟩ := hmem p
    refine ⟨Sigma.ι V p q, ?_⟩
    rw [← Scheme.Hom.comp_apply, hιf, hq]
  · obtain ⟨a, ha⟩ := (sec_sigma_bijective R ((res R F).X (n - 1)) V).2 y
    have hda : Sec.map ((res R F).d (n - 1) n) a = Sec.res f z := by
      apply (sec_sigma_bijective R ((res R F).X n) V).1
      funext i
      have hai : Sec.res (Sigma.ι V i) a = y i := congrFun ha i
      change Sec.res (Sigma.ι V i) (Sec.map _ a) = Sec.res (Sigma.ι V i) (Sec.res f z)
      rw [← secMap_secRes_comm, hai, hy, secRes_secRes, hιf]
    have hY := GlobalTheory.T.cocycle_ev_d_eq_zero_and_mk_eq_zero_iff R (∐ V) (res R F) (n - 1) n (n + 1) (by omega) rfl
    have hev := GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties R (E := sch.obj X) (I := res R F) (n := n)
    let α' : Cocycle ((chains R).obj (sch.obj (∐ V))) (res R F) n :=
      zcomp (Cocycle.ofHom ((chains R).map (sch.map f))) α (zero_add n)
    change CohomologyClass.mk α' = 0
    rw [(hY.2 α').2]
    refine ⟨a, ?_⟩
    rw [hda]
    have h1 := (hev.2.2.2.1 (sch.map f) α.1 0 n (by simp) (∐ V) (𝟙 (∐ V)))
    have h2 := (hev.2.1 α.1 0 n (by simp) (∐ V) X f (𝟙 X))
    change _ = ev ((Cochain.ofHom ((chains R).map (sch.map f))).comp α.1 (zero_add n)) 0 n _ (∐ V) (𝟙 (∐ V))
    rw [h1, hz, h2]
    rfl

end GlobalTheory.EtC
end

section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport
open GlobalTheory.ToricTransport (coordIn)
open scoped nonZeroDivisors

theorem _root_.GlobalTheory.T.finiteIdele_module_exists_rat : ∀ {E : Type} [Field E] [NumberField E] (y : (Af E)ˣ), ∃ q : ℚ, modF y = q := by
  first | exact @GlobalTheory.CMVal.ModFRat.modF_rat | exact GlobalTheory.CMVal.ModFRat.modF_rat | (intros; apply GlobalTheory.CMVal.ModFRat.modF_rat <;> assumption)
end

section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory.CmpB

theorem blk_transpose {R : Type} [CommRing R] (d k : ℕ) (u v : R) :
    (blk d k u v).transpose = blk d k u v := Matrix.diagonal_transpose _

theorem tau_dvd_entry {R : Type} [CommRing R] (t : R) {m n h : Type} [Fintype n]
    (A : Matrix m n R) (Y : Matrix n h R) (hA : ∀ i j, t ∣ A i j) (i : m) (j : h) :
    t ∣ (A * Y) i j := by
  rw [Matrix.mul_apply]
  exact Finset.dvd_sum fun l _ => dvd_mul_of_dvd_left (hA i l) _

theorem comparison : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ F : BFrame ε, ∀ (d k h : ℕ) (U U' X : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) F.B) (Y Z : Matrix (Fin d ⊕ Fin k) (Fin h) F.B), IsUnit U' → IsNil F.θ F.σ (U'.transpose⁻¹ * blk d k 1 (p : F.B)) → IsNil F.θ F.σ (U' * blk d k (p : F.B) 1) → X * (U' * blk d k (p : F.B) 1) = U * blk d k (p : F.B) 1 * X.map F.σ → (∀ i j, F.τ ∣ X i j - (1 : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) F.B) i j) → Y.map F.σ = blk d k (p : F.B) 1 * U.transpose * Y → Z.map F.σ = blk d k (p : F.B) 1 * U'.transpose * Z → (∀ i m, F.τ ∣ Z i m - Y i m) → Z = X.transpose * Y := by
  intro p _ C _ _ _ v O _ _ _ _ _ hv ε hε F d k h U U' X Y Z hU' hn1 hn2 hX hX1 hY hZ hZY
  set P := blk d k (p : F.B) 1 with hP

  have hT : P * U'.transpose * X.transpose = (X.map F.σ).transpose * P * U.transpose := by
    have := congrArg Matrix.transpose hX
    simp only [Matrix.transpose_mul, hP, blk_transpose] at this
    simpa only [Matrix.mul_assoc] using this
  have hΔ : (Z - X.transpose * Y).map F.σ = P * U'.transpose * (Z - X.transpose * Y) := by
    have e1 : (X.transpose * Y).map F.σ = P * U'.transpose * (X.transpose * Y) := by
      rw [Matrix.map_mul, Matrix.transpose_map, hY, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
        ← Matrix.mul_assoc, ← hT, Matrix.mul_assoc (P * U'.transpose)]
    rw [Matrix.map_sub _ (map_sub F.σ), hZ, e1, Matrix.mul_sub]
  have hdiv : ∀ i m, F.τ ∣ (Z - X.transpose * Y) i m := by
    intro i m
    have e : Z - X.transpose * Y = (Z - Y) - (X.transpose - 1) * Y := by
      rw [Matrix.sub_mul, Matrix.one_mul]; abel
    rw [e, Matrix.sub_apply]
    refine dvd_sub (by simpa using hZY i m) (tau_dvd_entry _ _ _ (fun a b => ?_) i m)
    have h1 : (1 : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) F.B) a b = (1 : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) F.B) b a := by
      simp only [Matrix.one_apply, eq_comm]
    rw [Matrix.sub_apply, Matrix.transpose_apply, h1]
    exact hX1 b a
  have := (GlobalTheory.T.ainfSquareZeroFrame_invariant_eq_zero_of_tau_dvd p C v O hv ε hε F d k h U' hU' hn1 hn2).1 _ hΔ hdiv
  exact (sub_eq_zero.1 this)

end GlobalTheory.CmpB
end

section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

theorem _root_.GlobalTheory.T.ainfFrame_solution_mul_congr_Gm_transpose : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ F : BFrame ε, ∀ (d k h : ℕ) (U U' X : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) F.B) (u l : F.B) (Gm : Matrix (Fin h) (Fin d ⊕ Fin k) F.B) (W : Matrix (Fin d ⊕ Fin k) (Fin h) F.B), IsUnit U → IsNil F.θ F.σ (U.transpose⁻¹ * blk d k 1 (p : F.B)) → IsNil F.θ F.σ (U * blk d k (p : F.B) 1) → F.τ ∣ u - 1 → X * (U' * blk d k (p : F.B) 1) = U * blk d k (p : F.B) 1 * X.map F.σ → (∀ i j, F.τ ∣ X i j - (1 : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) F.B) i j) → F.σ l = u * l → F.τ ∣ l - 1 → U * blk d k (p : F.B) 1 * Gm.transpose.map F.σ = (p : F.B) • Gm.transpose → U' * blk d k (p : F.B) 1 * W.map F.σ = ((p : F.B) * u) • W → (∀ i m, F.τ ∣ W i m - Gm m i) → X * W = l • Gm.transpose := by
  first | exact @GlobalTheory.CmpG.comparison | exact GlobalTheory.CmpG.comparison | (intros; apply GlobalTheory.CmpG.comparison <;> assumption)
end

section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

theorem _root_.GlobalTheory.T.quasi_log_lift_pdiv_group_frame : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ F : BFrame ε, ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d) (μ' : Fin d → MvPowerSeries (Fin d ⊕ Fin d) F.B), IsLift F.θ μ' → (∀ i, map F.θ (μ' i) = c.μ i) → ∀ f : MvPowerSeries (Fin d) F.Q, QL μ' ⊤ f → QL μ' ⊤ (frob p F.s f) ∧ (In (RingHom.ker F.θ) (cob1 (up F.Q μ') f) → QL μ' (Ideal.span {(p : F.B)}) (frob p F.s f)) := by
  first | exact @GlobalTheory.QLog.ql_frob | exact GlobalTheory.QLog.ql_frob | (intros; apply GlobalTheory.QLog.ql_frob <;> assumption)
end

section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

theorem _root_.GlobalTheory.T.quasiLogarithm_levelOne_defect_frobenius_pow : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ F : BFrame ε, ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d) (μ' : Fin d → MvPowerSeries (Fin d ⊕ Fin d) F.B), IsLift F.θ μ' → (∀ i, map F.θ (μ' i) = c.μ i) → ∀ (f g : MvPowerSeries (Fin d) F.Q) (a b : MvPowerSeries (Fin d) F.B), QL μ' ⊤ f → QL μ' ⊤ g → In (⊤ : Ideal F.B) (frob p F.s f - g) → map (algebraMap F.B F.Q) a = defect μ' p f → map (algebraMap F.B F.Q) b = defect μ' p g → c.ev 1 (map F.θ b) - c.ev 1 (map F.θ a) ^ p ∈ Ideal.span (algebraMap O (G.A 1) '' {o | ¬IsUnit o}) := by
  first | exact @GlobalTheory.QLog.defect_frob_pow | exact GlobalTheory.QLog.defect_frob_pow | (intros; apply GlobalTheory.QLog.defect_frob_pow <;> assumption)
end
