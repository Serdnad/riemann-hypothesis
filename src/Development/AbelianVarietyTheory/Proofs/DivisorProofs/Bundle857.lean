module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ComparisonMemCechHodgeFiltration
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Development.AbelianVarietyTheory.Definitions.Divisors.CrystallineConnectionFormCoboundaryZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.FderivFnCongr
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle004
public import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
public import Development.AbelianVarietyTheory.Definitions.Divisors.EllFamNontrivial
public import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle005
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiLogarithmPeriodFrobeniusTwist
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WindowLiftToFontaineAinfMatrices
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle551
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle554
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqZeroOfCobOneEqZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle501
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle725
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle648
public import Mathlib.Algebra.DualNumber
public import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle828
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle021
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle012
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
import Development.AbelianVarietyTheory.Definitions.Divisors.Pullback1MemHodgeFiltration
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.SpanXLeKerAevalZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001

@[expose] public section

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.DeRham

namespace GlobalTheory.PointSec

theorem exists_affine_map_ne_top : ∀ (R' : Type) [CommRing R'] (X X' : Scheme.{0}) (s' : X' ⟶ Sp R') (φ : X' ⟶ X), Surjective s' → ∀ m : Ideal R', m.IsMaximal → ∃ U : X.affineOpens, Ideal.map (algebraMap R' (Sec s' (φ ⁻¹ᵁ U.1))) m ≠ ⊤ := by
  intro R' _ X X' s' φ hs m hm
  obtain ⟨x', hx'⟩ := hs.surj (⟨m, hm.isPrime⟩ : PrimeSpectrum R')
  obtain ⟨U, hU, hxU, -⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens)
    (show φ.base x' ∈ (⊤ : X.Opens) from trivial)
  refine ⟨⟨U, hU⟩, ?_⟩
  have hx : x' ∈ φ ⁻¹ᵁ U := hxU
  intro htop
  let g : Sec s' (φ ⁻¹ᵁ U) →+* X'.presheaf.stalk x' := (X'.presheaf.germ (φ ⁻¹ᵁ U) x' hx).hom
  have key : ∀ a ∈ m, ¬ IsUnit (g (algebraMap R' (Sec s' (φ ⁻¹ᵁ U)) a)) := by
    intro a ha hu
    have h1 : x' ∈ X'.basicOpen (algebraMap R' (Sec s' (φ ⁻¹ᵁ U)) a : Γ(X', φ ⁻¹ᵁ U)) :=
      (Scheme.mem_basicOpen _ _ _ hx).2 hu
    change x' ∈ X'.basicOpen ((X'.presheaf.map (homOfLE (le_top : φ ⁻¹ᵁ U ≤ s' ⁻¹ᵁ ⊤)).op)
      (s'.app ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R')).inv a))) at h1
    have h2 : x' ∈ X'.basicOpen (s'.app ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R')).inv a)) :=
      Scheme.basicOpen_restrict X' (homOfLE (le_top : φ ⁻¹ᵁ U ≤ s' ⁻¹ᵁ ⊤)) _ h1
    have h3 : x' ∈ s' ⁻¹ᵁ (Sp R').basicOpen ((Scheme.ΓSpecIso (CommRingCat.of R')).inv a) := by
      rw [Scheme.preimage_basicOpen]; exact h2
    have h4 : s'.base x' ∈ (Sp R').basicOpen ((Scheme.ΓSpecIso (CommRingCat.of R')).inv a) := h3
    rw [basicOpen_eq_of_affine] at h4
    have h2 : s'.base x' ∈ PrimeSpectrum.basicOpen a := h4
    rw [hx'] at h2
    exact h2 ha
  have hle : Ideal.map (algebraMap R' (Sec s' (φ ⁻¹ᵁ U))) m ≤
      (IsLocalRing.maximalIdeal (X'.presheaf.stalk x')).comap g := by
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    exact key a ha
  have h1 : (1 : Sec s' (φ ⁻¹ᵁ U)) ∈ (IsLocalRing.maximalIdeal (X'.presheaf.stalk x')).comap g :=
    hle (by rw [show Ideal.map (algebraMap R' (Sec s' (φ ⁻¹ᵁ U))) m = ⊤ from htop]; trivial)
  rw [Ideal.mem_comap, map_one] at h1
  exact (IsLocalRing.mem_maximalIdeal _).1 h1 isUnit_one
end GlobalTheory.PointSec
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.DeRham

namespace GlobalTheory.CechDR

theorem flat_sec (R' : Type) [CommRing R'] (X' : Scheme.{0}) (s' : X' ⟶ Sp R') (hs : Flat s')
    (U : X'.affineOpens) : Module.Flat R' (Sec s' U.1) := by
  have h1 : (s'.appLE ⊤ U.1 le_top).hom.Flat :=
    HasRingHomProperty.appLE (P := @Flat) s' hs ⟨⊤, isAffineOpen_top _⟩ U le_top
  have h0 : (Scheme.ΓSpecIso (CommRingCat.of R')).inv.hom.Flat :=
    RingHom.Flat.of_bijective (ConcreteCategory.bijective_of_isIso _)
  have h2 : (secMap s' U.1).hom.Flat := by
    exact RingHom.Flat.comp h0 h1
  exact h2

end GlobalTheory.CechDR
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.AnPer

theorem evalAt_fn_eq_valAt' {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (W : Opens E) {X : Scheme.{0}}
    (x : Sp (Hol W) ⟶ X) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) (f : Γ(X, U)) (p : E) (hp : p ∈ W) :
    ⊤ ≤ (spMap (Hol.ev p hp).toRingHom ≫ x) ⁻¹ᵁ U ∧
      (evalAt x U h f).fn p = valAt' (spMap (Hol.ev p hp).toRingHom ≫ x) U f := by
  set φ : Hol W →+* ℂ := (Hol.ev p hp).toRingHom
  have h' : ⊤ ≤ (spMap φ ≫ x) ⁻¹ᵁ U := fun q _ ↦ h (Set.mem_univ ((spMap φ) q))
  refine ⟨h', ?_⟩
  have e : (spMap φ ≫ x).appLE U ⊤ h' ≫ (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom =
      x.appLE U ⊤ h ≫ (Scheme.ΓSpecIso (CommRingCat.of (Hol W))).hom ≫ CommRingCat.ofHom φ := by
    rw [← Scheme.ΓSpecIso_naturality, ← Category.assoc,
      ← Scheme.Hom.appLE_comp_appLE (spMap φ) x U ⊤ ⊤ h le_rfl]
    congr 2
  have e2 := congrArg (fun t ↦ t.hom f) e
  rw [valAt', dite_eq_left h', valAt, ← Hol.ev_apply p hp]
  exact e2.symm

end GlobalTheory.AnPer
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

theorem _root_.GlobalTheory.T.etC_a2 : GlobalTheory.EtC.A2 := by
  first | exact @GlobalTheory.EtC.smooth_surjective_cech_descent_cohomology | exact GlobalTheory.EtC.smooth_surjective_cech_descent_cohomology | (intros; apply GlobalTheory.EtC.smooth_surjective_cech_descent_cohomology <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AnPer

theorem cup_per_sum_const {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ}
    (K : Charts F) {n : ℕ} (p q : Fin n → Λ →+ Hol F.V) (ℓ : GlobalTheory.CatCoh.Z2 K.Oc) (c : GlobalTheory.CatCoh.C1 K.Oc)
    (β : Λ → Λ → Hol F.V)
    (h : (∑ i, GlobalTheory.CatCoh.cup K.Oc (K.perCl (p i)) (K.perCl (q i))) = GlobalTheory.CatCoh.H2.mk K.Oc ℓ)
    (hℓ : ∀ (T T' T'' : K.Obj) (φ : T ⟶ T') (ψ : T' ⟶ T''), (show T''.C from ℓ.1 T T' T'' φ ψ) =
      (show T''.C from GlobalTheory.CatCoh.d1 K.Oc c T T' T'' φ ψ) + algebraMap (Hol F.V) T''.C (β φ.deg ψ.deg)) :
    ∃ c' : GlobalTheory.CatCoh.C1 K.Oc, ∀ (T T' T'' : K.Obj) (φ : T ⟶ T') (ψ : T' ⟶ T''),
      GlobalTheory.CatCoh.d1 K.Oc c' T T' T'' φ ψ =
        algebraMap (Hol F.V) (K.Oc.obj T'') (∑ i, p i φ.deg * q i ψ.deg - β φ.deg ψ.deg) := by
  simp only [Charts.perCl, GlobalTheory.CatCoh.cup_mk] at h
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← map_sum, GlobalTheory.CatCoh.H2.mk_eq_mk] at h
  obtain ⟨f, hf⟩ := h
  refine ⟨f + c, fun T T' T'' φ ψ ↦ ?_⟩
  have e := congrFun (congrFun (congrFun (congrFun (congrFun hf T) T') T'') φ) ψ
  have e2 := hℓ T T' T'' φ ψ
  rw [map_add (f := _), Pi.add_apply, Pi.add_apply, Pi.add_apply, Pi.add_apply, Pi.add_apply, e]
  rw [Pi.sub_apply, Pi.sub_apply, Pi.sub_apply, Pi.sub_apply, Pi.sub_apply, Submodule.coe_sum]
  simp only [Finset.sum_apply, GlobalTheory.CatCoh.cupZ_apply, Charts.perZ, Charts.mp_Oc] at e2 ⊢
  set_option synthInstance.maxHeartbeats 100000 in
    rw [e2, map_sub, map_sum]
  simp only [AlgHom.commutes, map_mul]
  ring

end GlobalTheory.AnPer
end

section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

theorem _root_.GlobalTheory.T.quasiLogarithm_period_frobenius_twist : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ F : BFrame ε, ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d) (μ' : Fin d → MvPowerSeries (Fin d ⊕ Fin d) F.B), IsLift F.θ μ' → (∀ i, map F.θ (μ' i) = c.μ i) → ∀ (f : MvPowerSeries (Fin d) F.Q) (t : G.Tate) (y : F.B), QL μ' ⊤ f → c.HasPeriod F.θ t f y → c.HasPeriod F.θ t (frob p F.s f) (F.σ y) := by
  first | exact @GlobalTheory.QLog.hasPeriod_frob | exact GlobalTheory.QLog.hasPeriod_frob | (intros; apply GlobalTheory.QLog.hasPeriod_frob <;> assumption)
end

section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

theorem _root_.GlobalTheory.T.window_lift_to_fontaineAinf_matrices : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ F : BFrame ε, ∀ (d k h : ℕ) (U : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) F.B) (Y : Matrix (Fin d ⊕ Fin k) (Fin h) F.B) (Gm : Matrix (Fin h) (Fin d ⊕ Fin k) F.B), IsUnit U ∧ Y.map F.σ = blk d k (p : F.B) 1 * U.transpose * Y ∧ U * blk d k (p : F.B) 1 * (Gm.transpose.map F.σ) = (p : F.B) • Gm.transpose ∧ Gm * Y = F.a (Sandwich.mu ε) • (1 : Matrix (Fin h) (Fin h) F.B) ∧ (∀ i m, F.θ (Y (Sum.inl i) m) = 0) ∧ (∀ m j, F.θ (Gm m (Sum.inr j)) = 0) ∧ IsNil F.θ F.σ (U * blk d k (p : F.B) 1) ∧ IsNil F.θ F.σ (U.transpose⁻¹ * blk d k 1 (p : F.B)) → ∃ (Fa : Matrix (Fin d ⊕ Fin k) (Fin h) (Ainf p O)) (Ga : Matrix (Fin h) (Fin d ⊕ Fin k) (Ainf p O)) (Ψ Ψ' : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) (Ainf p O)), Ga * Fa = Sandwich.mu ε • (1 : Matrix (Fin h) (Fin h) (Ainf p O)) ∧ Fa = Ψ * Fa.map (phiInv p O) ∧ Ψ * Ψ' = xi ε • (1 : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) (Ainf p O)) ∧ (∀ i m, WittVector.fontaineTheta O p (Fa i m) = F.θ (Y i m)) ∧ ∀ m i, WittVector.fontaineTheta O p (Ga m i) = F.θ (Gm m i) := by
  first | exact @GlobalTheory.WinLift.Top.window_lift | exact GlobalTheory.WinLift.Top.window_lift | (intros; apply GlobalTheory.WinLift.Top.window_lift <;> assumption)
end

section

set_option autoImplicit false

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

namespace GlobalTheory.QLog

theorem isLift_id_of_isLaw {O : Type} [CommRing O] {d : ℕ}
    {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) O} (h : IsLaw μ) : IsLift (RingHom.id O) μ := by
  refine ⟨h.const, h.unit, h.comm, ?_⟩
  simpa only [MvPowerSeries.map_id, RingHom.id_apply] using h

theorem defect_compat : ∀ (p : ℕ) [Fact p.Prime] (O E : Type) [CommRing O] [CommRing E] [Algebra O E], IsFrame p E (RingHom.id O) → ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d), ∀ (f : MvPowerSeries (Fin d) E), QL c.μ ⊤ f → (∀ n, ∃ s : MvPowerSeries (Fin d) O, map (algebraMap O E) s = defect c.μ n f ∧ constantCoeff s = 0) ∧ ∀ (n : ℕ) (s s' : MvPowerSeries (Fin d) O), map (algebraMap O E) s = defect c.μ (p ^ n) f → map (algebraMap O E) s' = defect c.μ (p ^ (n + 1)) f → ∃ z, c.ev (n + 1) s' = G.mulP n (c.ev n s) + (p : O) ^ n • z := by
  intro p _ O E _ _ _ hF G d c f hf
  have hD := QLogDefect.main p O O E (RingHom.id O) hF d c.μ (isLift_id_of_isLaw c.isLaw) ⊤ f hf
  have hex : ∀ n, ∃ s : MvPowerSeries (Fin d) O,
      map (algebraMap O E) s = defect c.μ n f ∧ constantCoeff s = 0 := fun n => by
    obtain ⟨s, -, hs⟩ := (T.coeffsInIdealOfPowerSeries_iff_image O E (Fin d) ⊤ _).1.1 (hD n).1
    refine ⟨s, hs, hF.inj ?_⟩
    have h0 : ∀ i, constantCoeff (up E (nmul c.μ n) i) = 0 := fun i => by
      simp [up, (hD n).2 i]
    rw [← constantCoeff_map, hs, map_zero, defect, map_sub,
      constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero h0) h0 hf.1]
    simp [hf.1]
  refine ⟨hex, fun n s s' hs hs' => ?_⟩
  obtain ⟨κ, -, hκ⟩ := (T.coeffsInIdealOfPowerSeries_iff_image O E (Fin d ⊕ Fin d) ⊤ _).1.1 hf.2.2
  obtain ⟨s₁, hs₁, -⟩ := hex p
  have h := ((T.integral_coboundary_representative_cocycle_rules O E d c.μ c.isLaw hF.inj f κ hκ).2.2 p s₁ hs₁).2 (p ^ n) s s' hs
    (by rw [← pow_succ]; exact hs')
  haveI := hF.complete
  refine ⟨c.ev (n + 1) s₁, ?_⟩
  rw [h, map_add (f := _), map_smul, (T.ev_subst_natMultiple_prime_pow_constant p O G d c n).2.2, Nat.cast_pow]
  exact add_comm _ _

end GlobalTheory.QLog
end

section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

namespace GlobalTheory.QLog

theorem cobOne_ev_defect_dvd : ∀ (p : ℕ) [Fact p.Prime] (O E : Type) [CommRing O] [CommRing E] [Algebra O E], IsFrame p E (RingHom.id O) → ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d), ∀ (f : MvPowerSeries (Fin d) E), QL c.μ ⊤ f → ∀ (n : ℕ) (s : MvPowerSeries (Fin d) O), map (algebraMap O E) s = defect c.μ (p ^ n) f → ∃ z, cobOne O (G.A n) (c.ev n s) = (p : O) ^ n • z := by
  intro p _ O E _ _ _ hF G d c f hf n s hs
  have : IsAdicComplete (Ideal.span {(p : O)}) O := hF.complete
  obtain ⟨hf0, -, hfc⟩ := hf
  obtain ⟨κ, -, hκ⟩ := ((series_in_ideal_iff_image O E (Fin d ⊕ Fin d) ⊤ _).1).1 hfc
  obtain ⟨-, hκ0, hrest⟩ := GlobalTheory.T.integral_coboundary_representative_cocycle_rules O E d c.μ c.isLaw hF.inj f κ hκ
  have hcob := (hrest (p ^ n) s hs).1
  refine ⟨c.ev₂ n κ, ?_⟩
  rw [← (GlobalTheory.T.formalChart_evalSquare_properties p O G d c n s).2.2.2, hcob, map_sub, map_smul,
    (GlobalTheory.T.ev_subst_natMultiple_prime_pow_constant p O G d c n).2.1 κ, hκ0 hf0, map_zero, sub_zero, Nat.cast_pow]

end GlobalTheory.QLog
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AnPer.Hol

def jet {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {W : Opens E} {p : E} (hp : p ∈ W) (v : E) :
    Hol W →ₐ[ℂ] DualNumber ℂ where
  toFun h := TrivSqZeroExt.inl (ev p hp h) + TrivSqZeroExt.inr (ev p hp (der v h))
  map_one' := by
    ext <;> simp
  map_mul' f g := by
    ext
    · simp
    · simp [Derivation.leibniz]; ring
  map_zero' := by
    ext <;> simp
  map_add' f g := by
    ext <;> simp <;> ring
  commutes' c := by
    ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl]

theorem jet_spec {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {W : Opens E} {p : E} (hp : p ∈ W)
    (v : E) (h : Hol W) : (jet hp v h).fst = h.fn p ∧ (jet hp v h).snd = fderiv ℂ h.fn p v := by
  constructor
  · change (TrivSqZeroExt.inl (ev p hp h) + TrivSqZeroExt.inr (ev p hp (der v h)) : DualNumber ℂ).fst = _
    simp [ev_apply]
  · change (TrivSqZeroExt.inl (ev p hp h) + TrivSqZeroExt.inr (ev p hp (der v h)) : DualNumber ℂ).snd = _
    simp [ev_apply, fn_der v h hp]

end GlobalTheory.AnPer.Hol

theorem GlobalTheory.AnPer.Hol.exists_jet_algHom : ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (W : Opens E) (p : E), p ∈ W → ∀ v : E, ∃ ρ : Hol W →ₐ[ℂ] DualNumber ℂ, ∀ h, (ρ h).fst = h.fn p ∧ (ρ h).snd = fderiv ℂ h.fn p v := by
  intro E _ _ W p hp v
  exact ⟨GlobalTheory.AnPer.Hol.jet hp v, GlobalTheory.AnPer.Hol.jet_spec hp v⟩
end
end

section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

theorem _root_.GlobalTheory.T.homogeneous_cocycle_additiveLaw_reduction_coboundary : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p] (d N : ℕ) (c : MvPowerSeries (Fin d ⊕ Fin d) k), 2 ≤ N → IsCoc (addLaw k d) c → (∀ γ : Fin d ⊕ Fin d →₀ ℕ, γ.degree ≠ N → coeff γ c = 0) → ∃ h : MvPowerSeries (Fin d) (Fr p k), (∀ α : Fin d →₀ ℕ, α.degree ≠ N → coeff α h = 0) ∧ Red p (cob1 (addLaw (Fr p k) d) h) c := by
  first | exact @GlobalTheory.LazardHomog.homogCoc_red_cob | exact GlobalTheory.LazardHomog.homogCoc_red_cob | (intros; apply GlobalTheory.LazardHomog.homogCoc_red_cob <;> assumption)
end

section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

theorem _root_.GlobalTheory.T.invariantDifferentials_connectedPDivGroup_coordinates : ∀ (p : ℕ) (k : Type) [CommRing k] (d : ℕ) (G : PDivGroup p k) (c : Chart G d), (∀ w : Fin d → k, (fun n => ∑ i, w i • dUnit (R := k) (c.x n i)) ∈ G.omegaSub) ∧ ∀ u : G.omega, ∃! w : Fin d → k, ∀ n, u.1 n = ∑ i, w i • dUnit (R := k) (c.x n i) := by
  first | exact @GlobalTheory.OmegaCoord.omega_coord | exact GlobalTheory.OmegaCoord.omega_coord | (intros; apply GlobalTheory.OmegaCoord.omega_coord <;> assumption)
end
