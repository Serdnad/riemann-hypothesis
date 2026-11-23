module

public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsLatFamilyCongr
public import Mathlib.Algebra.AffineMonoid.Basic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ArithmeticHilbertSamuelLowerBound
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle092
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle016
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.BundleObjects
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.InstFintypeSumElim
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.ClassListMapDomainPerm
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle002
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle044
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle056
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle025
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle064
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.CompactGapsGE
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Bundle001
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle001

@[expose] public section

section

open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT

namespace PositivityTheory.Xgn.SequenceCoordinates

theorem mem_of_loc {O Ω : Type} [CommRing O] [Field Ω] [Algebra O Ω] (R : Subalgebra O Ω) (x : Ω)
    (h : ∀ 𝔮 : Ideal R, 𝔮.IsPrime → ∃ u v : R, v ∉ 𝔮 ∧ x * (v : Ω) = (u : Ω)) : x ∈ R := by
  let I : Ideal R :=
    { carrier := {v | x * (v : Ω) ∈ R}
      add_mem' := fun {a b} ha hb => by
        have := R.add_mem ha hb
        simpa [mul_add] using this
      zero_mem' := by simpa using R.zero_mem
      smul_mem' := fun c v hv => by
        have := R.mul_mem c.2 hv
        simp only [smul_eq_mul, Set.mem_setOf_eq, MulMemClass.coe_mul]
        rwa [mul_left_comm] }
  have hI : I = ⊤ := by
    by_contra hne
    obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal I hne
    obtain ⟨u, v, hv, huv⟩ := h M hM.isPrime
    refine hv (hle ?_)
    show x * (v : Ω) ∈ R
    rw [huv]; exact u.2
  have h1 : (1 : R) ∈ I := hI ▸ Submodule.mem_top
  have h2 : x * ((1 : R) : Ω) ∈ R := h1
  simpa using h2

theorem mem_htW_iff {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {G : Over X} [GrpObj G]
    {Li : Type} [AddCommGroup Li] [Module Ω Li] (M : LieModel G ξ Li) (L : LB G.left) (n : ℕ)
    {B : Type} [CommRing B] (ρ : B →+* Module.End Ω Li) (σ : B →+* Ω) (𝔡 : Ideal B) (q : Cpt ξ)
    (hσ : ∀ d, σ d ∈ regAt ξ q) (x : B) (hx : x ∈ 𝔡) (o : Ω) (ho : o ∈ regAt ξ q) (hox : o * σ x = 1) (e : Li) :
    e ∈ M.htW L n ρ σ 𝔡 q ↔ e ∈ M.htDual L n ρ σ q := by
  constructor
  · intro he
    refine (Submodule.span_le.2 ?_ : M.htW L n ρ σ 𝔡 q ≤ M.htDual L n ρ σ q) he
    rintro e ⟨-, he⟩
    have h1 : o • σ x • e ∈ M.htDual L n ρ σ q := (M.htDual L n ρ σ q).smul_mem ⟨o, ho⟩ (he x hx)
    rw [smul_smul, hox, one_smul] at h1
    exact h1
  · intro he
    refine Submodule.subset_span ⟨M.mem_eigSp_of_mem_htDual L n ρ σ he, fun d _ => ?_⟩
    exact (M.htDual L n ρ σ q).smul_mem ⟨σ d, hσ d⟩ he

theorem span_apply_iff {Ω V : Type} [Field Ω] [AddCommGroup V] [Module Ω V] (R : Subring Ω)
    (T : Set (Module.Dual Ω V)) (e : V) :
    (∀ w ∈ Submodule.span R T, w e ∈ R) ↔ ∀ w ∈ T, w e ∈ R := by
  refine ⟨fun h w hw => h w (Submodule.subset_span hw), fun h w hw => ?_⟩
  induction hw using Submodule.span_induction with
  | mem x hx => exact h x hx
  | zero => simpa using R.zero_mem
  | add x y _ _ hx hy => simpa using R.add_mem hx hy
  | smul c x _ hx => exact R.mul_mem c.2 hx

end PositivityTheory.Xgn.SequenceCoordinates

theorem PositivityTheory.Xgn.sequence_coordinates_exist : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O₀ : Type) [CommRing O₀] (β : O₀ →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (d : ℕ), IsArithVar (mCoordIdeal y) (d + 1) → 0 < D.p + D.q → ∀ (p : ℕ) [Fact p.Prime], p ∈ S → ∀ (b : ∀ t, Fin (labelRk D t) → 𝔐.Li), (∀ t, LinearIndependent Ω (b t) ∧ Submodule.span Ω (Set.range (b t)) = 𝔐.Vgen t) → ∀ (A : Type) [CommRing A] [Algebra A Ω] [IsIntegralClosure A ℤ Ω] (m : Ideal A) [m.IsPrime], (p : A) ∈ m → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra A O] [IsLocalization.AtPrime O m] [Algebra O Ω] [IsScalarTower A O Ω], ∀ (G : GenTors 𝔐 p) (c' : ∀ k, J k), mseg y c' ≠ 0 → ∀ (P : ChartPack G O c'), ∀ (s : CMType H ⊕ CMType H), (∀ a : 𝓞 E, ∃ o : O, algebraMap O Ω o = 𝔐.emb s a) → (∃ x ∈ differentIdeal ℤ (𝓞 E), ∃ o : O, algebraMap O Ω o * 𝔐.emb s x = 1) → (∀ (q : Cpt 𝔐.ξ), InChart 𝔐.ξ (mseg y) c' q → (∀ o : O, algebraMap O Ω o ∈ regAt 𝔐.ξ q) → ∀ x ∈ CR O y c', x ∈ regAt 𝔐.ξ q) → (∀ 𝔮 : Ideal (CR O y c'), 𝔮.IsPrime → ∃ q : Cpt 𝔐.ξ, InChart 𝔐.ξ (mseg y) c' q ∧ (∀ o : O, algebraMap O Ω o ∈ regAt 𝔐.ξ q) ∧ ∀ x : Ω, x ∈ regAt 𝔐.ξ q ↔ ∃ u v : CR O y c', v ∉ 𝔮 ∧ x * (v : Ω) = (u : Ω)) → (∀ q : Cpt 𝔐.ξ, InChart 𝔐.ξ (mseg y) c' q → (∀ o : O, algebraMap O Ω o ∈ regAt 𝔐.ξ q) → HT.omP 𝔐 p q = Submodule.span (regAt 𝔐.ξ q) (P.Dh.om' : Set (Module.Dual Ω 𝔐.Li))) → ∀ a : Fin (labelRk D s) → Ω, a ∈ coordLat O y (𝔐.HT p s) (b s) c' ↔ ∀ u ∈ P.Dh.om', u (∑ k, a k • b s k) ∈ CR O y c' := by
  intro E _ _ _ H D l Xo c O₀ _ β Y S Ω _ K _ _ J _ y 𝔐 d _ _ p _ _ b hb A _ _ _ m _ _ O _ _ _ _ _ _ _ G c' _ P s
    hemb hdiff hCR hpr hloc a
  have he : (∑ k, a k • b s k) ∈ eigSp 𝔐.ρ (𝔐.emb s) := by
    have h := (hb s).2
    unfold HodgeCpt.Vgen at h
    rw [← h]
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  obtain ⟨x, hx, o, hox⟩ := hdiff
  have key : ∀ q : Cpt 𝔐.ξ, InChart 𝔐.ξ (mseg y) c' q → (∀ o : O, algebraMap O Ω o ∈ regAt 𝔐.ξ q) →
      ((∑ k, a k • b s k) ∈ 𝔐.HT p s q ↔ ∀ u ∈ P.Dh.om', u (∑ k, a k • b s k) ∈ regAt 𝔐.ξ q) := by
    intro q h1 h2
    have hD : (∑ k, a k • b s k) ∈ 𝔐.HT p s q ↔
        (∑ k, a k • b s k) ∈ 𝔐.M.htDual 𝔐.t.PP.L (p ^ 𝔐.R p) 𝔐.ρ (𝔐.emb s) q := by
      cases s with
      | inl τ =>
        refine PositivityTheory.Xgn.SequenceCoordinates.mem_htW_iff 𝔐.M 𝔐.t.PP.L (p ^ 𝔐.R p) 𝔐.ρ (𝔐.emb (.inl τ)) _ q
          (fun d => ?_) x hx _ (h2 o) hox _
        obtain ⟨o', ho'⟩ := hemb d
        rw [← ho']; exact h2 o'
      | inr τ => exact Iff.rfl
    rw [hD, LieModel.mem_htDual_iff, and_iff_right he]
    have hl : 𝔐.M.htOm 𝔐.t.PP.L (p ^ 𝔐.R p) q = _ := hloc q h1 h2
    rw [hl, PositivityTheory.Xgn.SequenceCoordinates.span_apply_iff]
    rfl
  have hm : a ∈ coordLat O y (𝔐.HT p s) (b s) c' ↔ ∀ q : Cpt 𝔐.ξ, InChart 𝔐.ξ (mseg y) c' q →
      (∀ o : O, algebraMap O Ω o ∈ regAt 𝔐.ξ q) → ∑ k, a k • b s k ∈ 𝔐.HT p s q := by
    simp [coordLat, AddSubgroup.mem_iInf, Fintype.linearCombination_apply]
  rw [hm]
  constructor
  · intro h u hu
    refine PositivityTheory.Xgn.SequenceCoordinates.mem_of_loc _ _ fun 𝔮 h𝔮 => ?_
    obtain ⟨q, h1, h2, h3⟩ := hpr 𝔮 h𝔮
    exact (h3 _).1 ((key q h1 h2).1 (h q h1 h2) u hu)
  · intro h q h1 h2
    exact (key q h1 h2).2 fun u hu => hCR q h1 h2 _ (h u hu)
end

section

open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT

namespace PositivityTheory.Xgn.FunctionAtPoint

theorem germ_frac {X : Scheme.{0}} {Ω : Type} [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) {R : Type} [CommRing R]
    (φ : R →+* Ω) (hφ : Function.Injective φ) (x : Spec (CommRingCat.of R) ⟶ X) (hx : spMap φ ≫ x = ξ)
    (z : Spec (CommRingCat.of R)) (hz : genPt ξ ⤳ x z) (a : X.presheaf.stalk (x z)) :
    ∃ r s : R, s ∉ z.asIdeal ∧ φ s * genMap ξ ⟨x z, hz⟩ a = φ r ∧ (r ∉ z.asIdeal → IsUnit a) := by
  haveI : z.asIdeal.IsPrime := PrimeSpectrum.isPrime z
  letI alg : Algebra R ((Spec (CommRingCat.of R)).presheaf.stalk z) := StructureSheaf.stalkAlgebra R z
  haveI loc : IsLocalization.AtPrime ((Spec (CommRingCat.of R)).presheaf.stalk z) z.asIdeal :=
    StructureSheaf.IsLocalization.to_stalk R z
  have hu : ∀ s : z.asIdeal.primeCompl, IsUnit (φ s) := by
    intro s
    refine IsUnit.mk0 _ fun h => s.2 ?_
    have h0 : (s : R) = 0 := hφ (h.trans (map_zero φ).symm)
    rw [h0]
    exact z.asIdeal.zero_mem
  let lam : (Spec (CommRingCat.of R)).presheaf.stalk z →+* Ω := IsLocalization.lift (M := z.asIdeal.primeCompl) hu
  let lam' : (Spec (CommRingCat.of R)).presheaf.stalk z ⟶ CommRingCat.of Ω := CommRingCat.ofHom lam
  have hlam : ∀ r : R, lam (algebraMap R _ r) = φ r := fun r => IsLocalization.lift_eq hu r
  have e0 : (Spec (CommRingCat.of R)).fromSpecStalk z =
      Spec.map (CommRingCat.ofHom (algebraMap R ((Spec (CommRingCat.of R)).presheaf.stalk z))) :=
    Spec.fromSpecStalk_eq' _ _
  have e1 : Spec.map (CommRingCat.ofHom lam) ≫ (Spec (CommRingCat.of R)).fromSpecStalk z = spMap φ := by
    rw [e0, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    exact RingHom.ext hlam
  have e2 : Spec.map (x.stalkMap z ≫ lam') ≫ X.fromSpecStalk (x z) = ξ := by
    rw [Spec.map_comp, Category.assoc, Scheme.SpecMap_stalkMap_fromSpecStalk]
    exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ x) e1).trans hx)
  have e3 : spMap (genMap ξ ⟨x z, hz⟩) ≫ X.fromSpecStalk (x z) = ξ :=
    GlobalTheory.CompanionTheory.Ar.LieStalk.spMap_genMap_fromSpecStalk ⟨x z, hz⟩
  have e4 : x.stalkMap z ≫ lam' = CommRingCat.ofHom (genMap ξ ⟨x z, hz⟩) :=
    Spec.map_injective ((cancel_mono (X.fromSpecStalk (x z))).1 (e2.trans e3.symm))
  have e5 : lam ((x.stalkMap z).hom a) = genMap ξ ⟨x z, hz⟩ a := ConcreteCategory.congr_hom e4 a
  obtain ⟨⟨r, s⟩, hrs⟩ := IsLocalization.surj z.asIdeal.primeCompl ((x.stalkMap z).hom a)
  refine ⟨r, s, s.2, ?_, fun hr => ?_⟩
  · rw [← e5, ← hlam, ← hlam, ← map_mul, mul_comm]
    exact congrArg lam hrs
  · have h1 : IsUnit (algebraMap R ((Spec (CommRingCat.of R)).presheaf.stalk z) r) :=
      IsLocalization.map_units _ (⟨r, hr⟩ : z.asIdeal.primeCompl)
    rw [← hrs] at h1
    exact isUnit_of_map_unit (x.stalkMap z).hom a (isUnit_of_mul_isUnit_left h1)

theorem inv_reg {X : Scheme.{0}} {Ω : Type} [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) {R : Type} [CommRing R]
    (φ : R →+* Ω) (hφ : Function.Injective φ) (x : Spec (CommRingCat.of R) ⟶ X) (hx : spMap φ ≫ x = ξ)
    (z : Spec (CommRingCat.of R)) (hz : genPt ξ ⤳ x z) {b : Ω} (hb : b ∈ regAt ξ ⟨x z, hz⟩) (w : R)
    (hw : φ w * b = 1) : φ w ∈ regAt ξ ⟨x z, hz⟩ := by
  obtain ⟨a, rfl⟩ := hb
  obtain ⟨r, s, hs, e, hu⟩ := germ_frac ξ φ hφ x hx z hz a
  have e1 : s = w * r := by
    apply hφ
    rw [map_mul, ← e, mul_left_comm, hw, _root_.mul_one]
  have hr : r ∉ z.asIdeal := fun h => hs (e1 ▸ z.asIdeal.mul_mem_left w h)
  obtain ⟨a', ha'⟩ := (hu hr).exists_right_inv
  refine ⟨a', ?_⟩
  have e2 := congrArg (genMap ξ ⟨x z, hz⟩) ha'
  rw [map_mul, map_one] at e2
  rw [← _root_.one_mul (genMap ξ ⟨x z, hz⟩ a'), ← hw, _root_.mul_assoc, e2, _root_.mul_one]

end PositivityTheory.Xgn.FunctionAtPoint

theorem PositivityTheory.Xgn.exists_function_at_point : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O₀ : Type) [CommRing O₀] (β : O₀ →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (d : ℕ), IsArithVar (mCoordIdeal y) (d + 1) → ∀ (p : ℕ) [Fact p.Prime], p ∈ S → ∀ (A : Type) [CommRing A] [Algebra A Ω] [IsIntegralClosure A ℤ Ω] (m : Ideal A) [m.IsPrime], (p : A) ∈ m → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra A O] [IsLocalization.AtPrime O m] [Algebra O Ω] [IsScalarTower A O Ω] (G : GenTors 𝔐 p) (c' : ∀ k, J k), mseg y c' ≠ 0 → ∀ (P : ChartPack G O c') (z : Spec (CommRingCat.of (CR O y c'))), InChart 𝔐.ξ (mseg y) c' ⟨P.x z, 𝔐.all _⟩ ∧ (∀ o : O, algebraMap O Ω o ∈ regAt 𝔐.ξ ⟨P.x z, 𝔐.all _⟩) ∧ ∀ a ∈ regAt 𝔐.ξ ⟨P.x z, 𝔐.all _⟩, ∃ r s : CR O y c', s ∉ z.asIdeal ∧ (s : Ω) * a = r := by
  intro E _ _ _ H D l Xo c O₀ _ β Y S Ω _ K _ _ J _ y 𝔐 d hd p _ _ A _ _ _ m _ _ O _ _ _ _ _ _ _ G c' hc' P z
  have hC : HasConstants ℤ A y := (GlobalTheory.T.arith_variety_coord_ideal E H D l Xo c O₀ β Y S Ω K J y 𝔐 d hd A).2.2.2.1
  have hφ : Function.Injective (algebraMap (CR O y c') Ω) := Subtype.val_injective
  have hinv := fun {b : Ω} (hb : b ∈ regAt 𝔐.ξ ⟨P.x z, 𝔐.all _⟩) (w : CR O y c') =>
    PositivityTheory.Xgn.FunctionAtPoint.inv_reg 𝔐.ξ _ hφ P.x P.x_gen z (𝔐.all _) hb w
  obtain ⟨c'', hc''⟩ : ∃ c'', InChart 𝔐.ξ (mseg y) c'' ⟨P.x z, 𝔐.all _⟩ := 𝔐.tie.cover ⟨P.x z, 𝔐.all _⟩
  have hA : ∀ a : A, algebraMap A Ω a ∈ regAt 𝔐.ξ ⟨P.x z, 𝔐.all _⟩ := fun a =>
    GlobalTheory.CompanionTheory.Ar.Fam.chartRing_le_regAt ℤ y c'' _ hc'' (fun o => by simp) (hC c'' hc''.1 a)
  refine ⟨⟨hc', fun j => ?_⟩, fun o => ?_, ?_⟩
  · have h1 : mseg y c'' / mseg y c' ∈ regAt 𝔐.ξ ⟨P.x z, 𝔐.all _⟩ :=
      hinv (hc''.2 c') ⟨mseg y c'' / mseg y c', Algebra.subset_adjoin ⟨c'', rfl⟩⟩ (by
        have h0 := hc''.1
        change mseg y c'' / mseg y c' * (mseg y c' / mseg y c'') = 1
        field_simp)
    have h2 := mul_mem (hc''.2 j) h1
    have h0 := hc''.1
    have e : mseg y j / mseg y c'' * (mseg y c'' / mseg y c') = mseg y j / mseg y c' := by field_simp
    rwa [e] at h2
  · obtain ⟨⟨a, s⟩, has⟩ := IsLocalization.surj m.primeCompl o
    obtain ⟨u, hu⟩ := (IsLocalization.map_units O s).exists_left_inv
    have h1 : algebraMap O Ω u ∈ regAt 𝔐.ξ ⟨P.x z, 𝔐.all _⟩ :=
      hinv (hA s) (algebraMap O (CR O y c') u) (by
        change algebraMap O Ω u * _ = 1
        rw [IsScalarTower.algebraMap_apply A O Ω, ← map_mul, hu, map_one])
    have e : o = algebraMap A O a * u := by
      have has' : o * algebraMap A O s = algebraMap A O a := has
      rw [← has', _root_.mul_assoc, mul_comm _ u, hu, _root_.mul_one]
    rw [e, map_mul, ← IsScalarTower.algebraMap_apply]
    exact mul_mem (hA a) h1
  · rintro _ ⟨a, rfl⟩
    obtain ⟨r, s, hs, e, -⟩ :=
      PositivityTheory.Xgn.FunctionAtPoint.germ_frac 𝔐.ξ _ hφ P.x P.x_gen z (𝔐.all _) a
    exact ⟨r, s, hs, e⟩
end

section

open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg liftVar fnField ck rootNum SameGeneric LatLE IsPull IsPullBC IsSubQuot QuotIso IsFrobPres FlagModel modelDeg)

namespace PositivityTheory.Xgn.A_join_model

section Trdeg

variable {O : Type} [CommRing O] {Ω : Type} [Field Ω] [Algebra O Ω]

theorem mem_of_mem_adjoin (F : Subfield Ω) (hO : ∀ c : O, algebraMap O Ω c ∈ F) {a : Ω}
    (ha : a ∈ Algebra.adjoin O (F : Set Ω)) : a ∈ F := by
  induction ha using Algebra.adjoin_induction with
  | mem w hw => exact hw
  | algebraMap c => exact hO c
  | add _ _ _ _ h1 h2 => exact add_mem h1 h2
  | mul _ _ _ _ h1 h2 => exact mul_mem h1 h2

theorem trdeg_add (hinj : Function.Injective (algebraMap O Ω)) (F F' : Subfield Ω) (hle : F ≤ F')
    (hO : ∀ c : O, algebraMap O Ω c ∈ F) {r : ℕ} (t : Fin r → Ω) (hind : AlgebraicIndependent F t)
    (hmem : ∀ i, t i ∈ F') (halg : ∀ v ∈ F', IsAlgebraic (IntermediateField.adjoin F (Set.range t)) v) :
    Algebra.trdeg O (Algebra.adjoin O (F' : Set Ω)) =
      Algebra.trdeg O (Algebra.adjoin O (F : Set Ω)) + r := by
  have hU : (F : Set Ω) ∪ (F' : Set Ω) = F' := Set.union_eq_right.2 hle
  have h := AdjoinTrdegAdd.proof O Ω hinj (F : Set Ω) (F' : Set Ω) (Fin r) t
    (by rintro _ ⟨i, rfl⟩; exact hmem i) ?_ ?_
  · rw [hU, Fintype.card_fin] at h
    exact h
  · let f : Algebra.adjoin O (F : Set Ω) →+* F :=
      (Algebra.adjoin O (F : Set Ω)).val.toRingHom.codRestrict F fun a => mem_of_mem_adjoin F hO a.2
    refine AlgebraicIndependent.of_ringHom_of_comp_eq f (RingHom.id Ω) hind ?_ ?_
    · intro a b hab
      exact Subtype.ext (congrArg (fun w : F => (w : Ω)) hab)
    · ext a; rfl
  · intro a ha
    have h1 : IsAlgebraic (Algebra.adjoin F (Set.range t)) a :=
      IntermediateField.isAlgebraic_adjoin_iff.1 (halg a ha)
    have hsub : ∀ w ∈ Algebra.adjoin F (Set.range t),
        w ∈ Algebra.adjoin O ((F : Set Ω) ∪ Set.range t) := by
      intro w hw
      induction hw using Algebra.adjoin_induction with
      | mem w hw => exact Algebra.subset_adjoin (Or.inr hw)
      | algebraMap c => exact Algebra.subset_adjoin (Or.inl c.2)
      | add _ _ _ _ h1 h2 => exact add_mem h1 h2
      | mul _ _ _ _ h1 h2 => exact mul_mem h1 h2
    let f : Algebra.adjoin F (Set.range t) →+* Algebra.adjoin O ((F : Set Ω) ∪ Set.range t) :=
      (Algebra.adjoin F (Set.range t)).val.toRingHom.codRestrict _ fun w => hsub w w.2
    refine IsAlgebraic.ringHom_of_comp_eq f (RingHom.id Ω) h1 ?_ ?_
    · intro a b hab
      exact Subtype.ext (congrArg (fun w : Algebra.adjoin O ((F : Set Ω) ∪ Set.range t) => (w : Ω)) hab)
    · ext a; rfl

end Trdeg

section Model

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {Ω : Type} [Field Ω] [Algebra O Ω]
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]


omit [IsDomain O] [IsDiscreteValuationRing O] [Fintype K] [DecidableEq K] [∀ k, Fintype (ι k)] in
theorem comap_eq_ker (y : (Σ k, ι k) → Ω) :
    (pointIdeal O y).comap (C : O →+* MRing ι O) = RingHom.ker (algebraMap O Ω) := by
  ext a
  simp [pointIdeal, RingHom.mem_ker, pointConeMap, MvPolynomial.algebraMap_apply]

theorem dim_eq (hinj : Function.Injective (algebraMap O Ω)) (y : (Σ k, ι k) → Ω)
    (hy : ∀ k, ∃ i, y ⟨k, i⟩ ≠ 0) :
    ringKrullDim (MRing ι O ⧸ pointIdeal O y) =
      (((Algebra.trdeg O (Algebra.adjoin O (fnField O y : Set Ω))).toENat +
        ((1 + Fintype.card K : ℕ) : ℕ∞) : ℕ∞) : WithBot ℕ∞) := by
  have h1 := DvrConeDimTrdeg.proof O K ι (pointIdeal O y)
    (GenericProjClosureDim.isMultiProjPrime_pointIdeal (R := O) _ hy)
    (by rw [comap_eq_ker]; exact (RingHom.injective_iff_ker_eq_bot _).1 hinj)
  have h2 : Algebra.trdeg O (MRing ι O ⧸ pointIdeal O y) = _ := ConeTrdegFnField.proof O Ω hinj K ι y hy
  rw [h1, h2, map_add (f := _), map_natCast]
  congr 1
  push_cast
  ring

theorem isModelOver_iff (y : (Σ k, ι k) → Ω) (d : ℕ) :
    GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (mcIdeal O y) d ↔
      Nonempty K ∧ (∀ k, ∃ i, y ⟨k, i⟩ ≠ 0) ∧ Function.Injective (algebraMap O Ω) ∧
        (Algebra.trdeg O (Algebra.adjoin O (fnField O y : Set Ω))).toENat = d := by
  have key : ∀ T : ℕ∞, ((T + ((1 + Fintype.card K : ℕ) : ℕ∞) : ℕ∞) : WithBot ℕ∞) =
      ((d + 1 + Fintype.card K : ℕ) : WithBot ℕ∞) ↔ T = d := by
    intro T
    have e : ((d + 1 + Fintype.card K : ℕ) : WithBot ℕ∞) =
        (((d : ℕ∞) + ((1 + Fintype.card K : ℕ) : ℕ∞) : ℕ∞) : WithBot ℕ∞) := by
      rw [add_assoc, ← Nat.cast_add]; rfl
    rw [e, WithBot.coe_inj]
    exact ⟨fun h => WithTop.add_right_cancel (ENat.natCast_ne_top _) h, fun h => by rw [h]⟩
  constructor
  · intro h
    have hy := JoinTwoModels.exists_ne_zero y h
    rw [BundleExamples.mcIdeal_eq_pointIdeal, BundleExamples.isModelOver_iff] at h
    have hinj : Function.Injective (algebraMap O Ω) := by
      rw [RingHom.injective_iff_ker_eq_bot, ← comap_eq_ker y]
      exact h.2.noTorsion
    refine ⟨h.1, hy, hinj, (key _).1 ?_⟩
    rw [← dim_eq hinj y hy]
    exact h.2.dim
  · rintro ⟨hK, hy, hinj, hT⟩
    rw [BundleExamples.mcIdeal_eq_pointIdeal, BundleExamples.isModelOver_iff]
    refine ⟨hK, GenericProjClosureDim.isMultiProjPrime_pointIdeal (R := O) _ hy, ?_, ?_⟩
    · rw [comap_eq_ker]; exact (RingHom.injective_iff_ker_eq_bot _).1 hinj
    · rw [dim_eq hinj y hy]
      exact (key _).2 hT

end Model

end PositivityTheory.Xgn.A_join_model

theorem PositivityTheory.Xgn.t_join_model : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω) (d r : ℕ), GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (mcIdeal O x) d → ∀ (K' : Type) [Fintype K'] [DecidableEq K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (z : (Σ k, ι' k) → Ω), (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) → ∀ t : Fin r → Ω, AlgebraicIndependent (fnField O x) t → (∀ i, t i ∈ fnField O (joinCoord x z)) → (∀ v ∈ fnField O (joinCoord x z), IsAlgebraic (IntermediateField.adjoin (fnField O x) (Set.range t)) v) → GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (mcIdeal O (joinCoord x z)) (d + r) := by
  intro O _ _ _ Ω _ _ K _ _ ι _ x d r hx K' _ _ ι' _ z hz t hind hmem halg
  obtain ⟨hK, hx0, hinj, hT⟩ := (PositivityTheory.Xgn.A_join_model.isModelOver_iff x d).1 hx
  refine (PositivityTheory.Xgn.A_join_model.isModelOver_iff (joinCoord x z) (d + r)).2 ⟨inferInstance, ?_, hinj, ?_⟩
  · rintro (k | k)
    · exact hx0 k
    · exact hz k
  · have hle : fnField O x ≤ fnField O (joinCoord x z) := by
      refine Subfield.closure_le.2 ?_
      rintro _ (⟨a, rfl⟩ | ⟨⟨k, i, j⟩, rfl⟩)
      · exact Subfield.subset_closure (Or.inl ⟨a, rfl⟩)
      · exact Subfield.subset_closure (Or.inr ⟨⟨.inl k, (i, j)⟩, rfl⟩)
    rw [PositivityTheory.Xgn.A_join_model.trdeg_add hinj _ _ hle
      (fun c => Subfield.subset_closure (Or.inl ⟨c, rfl⟩)) t hind hmem halg, map_add, map_natCast, hT,
      Nat.cast_add]
end
