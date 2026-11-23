module

public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle006
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle003
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.TopAmpExists
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle002
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsHomBirationalModelsAmpleFrames
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.DenseOfDenseP
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle004
public import Development.AbelianVarietyTheory.Counterexamples.ModuliSurvey.PremisesOfProper
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle005
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle173
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CmFamilyFiniteUnramifiedOverSiegelFamily
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle126
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle146
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle009
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle174
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle169
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle068
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle076
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle116
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle151
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.TorsionSectionCoordsThetaTimesRoots
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSemiAbelianTripleGlueCommonGenericPart
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle002
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ZM

theorem _root_.GlobalTheory.T.exists_hom_birational_models_ampleFrames : GlobalTheory.LN.HomExtSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] (Z₁ Z₂ W : Scheme.{0}) (s₁ : Z₁ ⟶ Sp R) (s₂ : Z₂ ⟶ Sp R) (t₁ : SAB H Z₁) (t₂ : SAB H Z₂) (tW : SAB H W) (j : W ⟶ Z₁) (j' : W ⟶ Z₂) (_ : SABMap tW t₁ j) (_ : SABMap tW t₂ j') (N : ℕ) (A₁ : GlobalTheory.LN.AmpFrames t₁.G t₁.PP.L N) (A₂ : GlobalTheory.LN.AmpFrames t₂.G t₂.PP.L N), IsDedekindDomain R → CharZero R → Algebra.FiniteType ℤ R → IsNormalScheme Z₁ → IsProjOver s₁ → IsProjOver s₂ → Flat s₁ → IsPreimmersion j → Flat j → IsDominant j → QuasiCompact j → IsPreimmersion j' → Flat j' → IsDominant j' → QuasiCompact j' → IsProper tW.G.hom → j ≫ s₁ = j' ≫ s₂ → A₁.r = A₂.r → A₁.s = A₂.s → ∃ ρ : Z₁ ⟶ Z₂, j ≫ ρ = j' := by
  first | exact @GlobalTheory.AmpUniq.exists_hom_of_ampFrames | exact GlobalTheory.AmpUniq.exists_hom_of_ampFrames | (intros; apply GlobalTheory.AmpUniq.exists_hom_of_ampFrames <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

theorem _root_.GlobalTheory.T.exists_thetaObject_of_polarisedLattice : Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ThetaUnifAV → ∀ (o : Type) [CommRing o] (g k : ℕ) (J : Type) (b : TBase o k) (em : o →+* ℂ) (w w' : J) (La : Type) [AddCommGroup La] (EF : LinearMap.BilinForm ℤ La) (lam : Fin (2 * g) → La) (ac : J → La → La) (Q : La →+ (Fin g → ℂ)) (Hm : Matrix (Fin g) (Fin g) ℂ), Function.Bijective EF → (Function.Injective Q ∧ DiscreteTopology (Q).range ∧ Submodule.span ℝ (Set.range Q) = ⊤ ∧ (Hm).IsHermitian ∧ (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) ∧ ∀ x y, (hermForm Hm (Q x) (Q y)).im = EF x y) → (∀ j, ∃ F : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ), ∀ x, F (Q x) = Q (ac j x)) → (∀ x, ac w x + ac w' x = x) → (∀ x y, EF (ac w x) y = EF x (ac w' y)) → (∀ i₁ i₂, Complex.exp (-(2 * Real.pi * Complex.I) * (EF (lam i₁) (lam i₂) : ℂ) / ((k : ℕ) : ℂ)) = em (b.ζ : o) ^ Out.stdSymp g i₁ i₂) → ∃ t : TObj g k J b (spMap em), t.Prim w w' ∧ (∃ (u : HolUnif t.A t.L g) (χ' : u.Λ → ℂ), u.IsAH Hm χ' ∧ (∀ z, z ∈ u.Λ ↔ z ∈ (Q).range) ∧ (∀ x (l : u.Λ), (l : Fin g → ℂ) = Q x → χ' l = (-1) ^ EF x (ac w x)) ∧ (∀ i₀, (t.pt i₀).left = (u.ex (((k : ℕ) : ℂ)⁻¹ • Q (lam i₀))).left) ∧ ∀ j₀, ∃ F : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ), (∀ x, F (Q x) = Q (ac j₀ x)) ∧ ∀ z, u.ex (F z) = u.ex z ≫ t.act j₀) := by
  first | exact @GlobalTheory.thetaObject_of_lattice | exact GlobalTheory.thetaObject_of_lattice | (intros; apply GlobalTheory.thetaObject_of_lattice <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

theorem _root_.GlobalTheory.T.exists_siegelFamily_localised_cyclotomic_integers : Out.Laws → Out.Laws2 → ∀ (h k p : ℕ) (o : Type) [CommRing o] (ζ : o) (j : o →+* ZP p k), Odd k → 3 ≤ k → p.Prime → Function.Injective j → j ζ = zetaZP p k → (∀ (K : Type) [Field K] (y : Sp (DualNumber K) ⟶ Sp (ZP p k)), y = constPt y) → Algebra.IsAlgebraic ℤ o → SFam h k ζ → ∃ Ag : SiegelFamily h p k, SRep Ag := by
  first | exact @GlobalTheory.SiegelFamilyBaseChange.exists_siegelFamily | exact GlobalTheory.SiegelFamilyBaseChange.exists_siegelFamily | (intros; apply GlobalTheory.SiegelFamilyBaseChange.exists_siegelFamily <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

theorem _root_.GlobalTheory.T.embeddedAbelianVariety_cutOut_by_torsionForms : Out.Laws → Out.Laws2 → ∀ (g : ℕ) (J : Type) [Finite J] (Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) (κ n : ℕ), n.Prime → Odd n → ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ (o : Type) [CommRing o] (b : TBase o ((n ^ j) ^ 2)), ∃ (Hh : Type) (_ : Finite Hh) (hh : Hh → Ix g ((n ^ j) ^ 2)) (Q : Polynomial ℚ) (d : ℕ), ∀ (K : Type) [Field K] [IsAlgClosed K] (β : o →+* K) (t : TObj g ((n ^ j) ^ 2) J b (spMap β)) σ (p : Hh → Ix g ((n ^ j) ^ 2) → K), t.Emb (n ^ 2) (Over.mk (𝟙 _)) σ → (∀ h, SecCoord _ σ (lift (𝟙 (Over.mk (𝟙 (Sp K)))) (t.lab (hh h) ^ n ^ j)).left (p h)) → CutBy (idealOf (fst (Over.mk (𝟙 (Sp K))) t.A).left _ σ (𝟙 _)) Q d p := by
  first | exact @GlobalTheory.cutBy_embedded_abelian | exact GlobalTheory.cutBy_embedded_abelian | (intros; apply GlobalTheory.cutBy_embedded_abelian <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ZM

theorem _root_.GlobalTheory.T.cmFamily_finite_unramified_over_siegelFamily : GlobalTheory.LN.HomExtSt → Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (n N : ℕ) (MM : Scheme.{0}) (sM : MM ⟶ Sp (RZ H n N)) (tM : SAB H MM) (lev : D.La → (𝟙_ (Over MM) ⟶ tM.G)), 1 ≤ D.p + D.q → n.Prime → Odd n → (∃ j, 1 ≤ j ∧ N = n ^ j) → FamCore D sM tM lev → (∀ p : ℕ, p.Prime → p ≠ n → ∃ Ag : SiegelFamily (Module.finrank ℚ E / 2 * (D.p + D.q)) p N, SiegRep Ag) → SiegClause D sM tM lev := by
  first | exact @GlobalTheory.siegClause_of_famCore | exact GlobalTheory.siegClause_of_famCore | (intros; apply GlobalTheory.siegClause_of_famCore <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
open GlobalTheory.ZM.NearBuild

noncomputable section
namespace GlobalTheory.ZM.GoodFibre

theorem spMap_id (R : Type) [CommRing R] : spMap (RingHom.id R) = 𝟙 (Sp R) := by
  simp [spMap, Sp]

theorem exists_retraction {K R' : Type} [Field K] [CommRing R'] (φ : K →+* R') (hφ : IsOpenImmersion (spMap φ))
    (p : Sp K) (hp : p ∈ Set.range (spMap φ)) : ∃ ψ : R' →+* K, ψ.comp φ = RingHom.id K := by
  have hsurj : Function.Surjective (spMap φ) := by
    intro q
    obtain ⟨r, hr⟩ := hp
    exact ⟨r, Subsingleton.elim _ _⟩
  haveI : Surjective (spMap φ) := ⟨hsurj⟩
  haveI : IsIso (spMap φ) := (isIso_iff_isOpenImmersion_and_surjective _).2 ⟨hφ, inferInstance⟩
  obtain ⟨ψ', hψ'⟩ := Spec.map_surjective (inv (spMap φ))
  refine ⟨ψ'.hom, ?_⟩
  have key : Spec.map (CommRingCat.ofHom φ ≫ ψ') = Spec.map (𝟙 _) := by
    rw [Spec.map_comp, hψ', Spec.map_id]
    exact IsIso.inv_hom_id (spMap φ)
  have := Spec.map_injective key
  ext a
  exact congrArg (fun f => f.hom a) this

theorem secCoord_of_local {X : Scheme.{0}} {M : LB X} (hM : M.IsLB) {I : Type} {th : I → M.Sec} {K R' : Type} [Field K]
    [CommRing R'] {y : Sp K ⟶ X} {v : I → K} (φ : K →+* R') (hφ : IsOpenImmersion (spMap φ)) (p : Sp K)
    (hp : p ∈ Set.range (spMap φ)) (h : SecCoord M th (spMap φ ≫ y) (fun i => φ (v i))) : SecCoord M th y v := by
  obtain ⟨ψ, hψ⟩ := exists_retraction φ hφ p hp
  have h' := GlobalTheory.ZM.Coord.baseChange h ψ
  have e1 : spMap ψ ≫ spMap φ ≫ y = y := by
    rw [← Category.assoc, GlobalTheory.ZM.spMap_comp_ringHom_comp, hψ, spMap_id, Category.id_comp]
  have e2 : (fun i => ψ (φ (v i))) = v :=
    funext fun i => congrArg (fun f : K →+* K => f (v i)) hψ
  rw [e1, e2] at h'
  exact h'

theorem span_theta (l1 : Out.Laws) (l2 : Out.Laws2) {o : Type} [CommRing o] {g N' : ℕ} {J : Type} {b : TBase o (N' ^ 2)}
    {K : Type} [Field K] {s : Sp K ⟶ Sp o} (t : TObj g (N' ^ 2) J b s) (n : ℕ) (v : Ix g (N' ^ 2) → K)
    (h2 : 2 ≤ n) (hn : n ∣ N') (hth : t.HasTh (𝟙 _) v) : Ideal.span (Set.range v) = ⊤ := by
  by_contra hne
  obtain ⟨q, hq, hle⟩ := Ideal.exists_le_maximal _ hne
  have hc := GlobalTheory.coset_of_hasTh l1 l2 o g N' J b (Sp K) s t n K (𝟙 _) v q h2 hn hth hq.isPrime
  unfold Coset at hc
  obtain ⟨c, hc⟩ := hc 0
  exact hc (hle (Ideal.subset_span ⟨_, rfl⟩))

theorem exists_fibData : Out.Laws → Out.Laws2 → ∀ (g : ℕ) (J : Type) [Finite J] (Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) (κ n : ℕ), n.Prime → Odd n → ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ (o : Type) [CommRing o] (b : TBase o ((n ^ j) ^ 2)) (R : Type) [CommRing R] (β : o →+* R) (v : Ix g ((n ^ j) ^ 2) → R), ∃ (p : Ix g ((n ^ j) ^ 2) → Ix g ((n ^ j) ^ 2) → R) (Hh : Type) (_ : Finite Hh) (hh : Hh → Ix g ((n ^ j) ^ 2)) (Q : Polynomial ℚ) (d : ℕ), FibData b Mat κ β v (n ^ 2) p hh Q d := by
  intro l1 l2 g J _ Mat κ n hn hodd
  obtain ⟨j₁, hj₁⟩ := GlobalTheory.cutBy_embedded_abelian l1 l2 g J Mat κ n hn hodd
  refine ⟨max j₁ 4, fun j hj o _ b R _ β v => ?_⟩
  have hjc : j₁ ≤ j := le_of_max_le_left hj
  have hj4 : 4 ≤ j := le_of_max_le_right hj
  have hoddN : Odd (n ^ j) := hodd.pow
  have hdvd : n ^ 2 ∣ n ^ j := pow_dvd_pow n (by omega)
  have hdvd2 : (n ^ 2) ^ 2 ∣ n ^ j := by
    rw [← pow_mul]
    exact pow_dvd_pow n (by omega)
  have htwo : 2 ≤ n ^ 2 := le_trans hn.two_le (Nat.le_self_pow (by norm_num) n)
  obtain ⟨e, idx, hto⟩ := GlobalTheory.torsion_secCoord l1 l2 g (n ^ 2) (n ^ j) hoddN hdvd2
  obtain ⟨Hh, hfin, hh, Q, d, hcut⟩ := hj₁ j hjc o b
  refine ⟨fun h a => β (b.ζ ^ e a h : oˣ) * v (idx a h), Hh, hfin, hh, Q, d, ?_⟩
  intro K _ _ x s t hgood
  obtain ⟨hs, -, hth⟩ := hgood
  rw [GlobalTheory.ZM.spMap_comp_ringHom_comp] at hs
  subst hs
  obtain ⟨σ, hemb, hproj⟩ := GlobalTheory.T.exists_embeddingSections_over_field l1 l2 o g (n ^ j) J b K _ t (n ^ 2) (fun a => x (v a)) hdvd2 htwo hth
  have hLB := (GlobalTheory.T.thetaSections_veryAmple_periodic l1 l2 o g (n ^ j) J b K (x.comp β) t (n ^ 2) σ hoddN hdvd htwo hemb).2.1
  have hspan : Ideal.span (Set.range fun a => x (v a)) = ⊤ :=
    span_theta l1 l2 t n (fun a => x (v a)) hn.two_le (dvd_pow_self n (by omega)) hth
  have hsec : ∀ h, SecCoord _ σ (lift (𝟙 (Over.mk (𝟙 (Sp K)))) (t.lab h ^ n ^ j)).left
      (fun a => x (β (b.ζ ^ e a h : oˣ) * v (idx a h))) := by
    intro h
    have hy : ((Over.homMk (𝟙 (Sp K)) (by simp) : Over.mk (𝟙 (Sp K)) ⟶ Out.baseOver (Sp K)) ≫ t.lab h)
        = t.lab h := by
      ext
      simp
    obtain ⟨R', _, φ, hφ, hp, hc⟩ := hto o J b (Sp K) _ t K (x.comp β) (𝟙 _) (fun a => x (v a)) σ
      (Category.id_comp _) hth hspan hemb h _ (by rw [hy]) (IsLocalRing.closedPoint K)
    have key := secCoord_of_local hLB φ hφ _ hp hc
    have hv : (fun a => x (β (b.ζ ^ e a h : oˣ) * v (idx a h)))
        = (fun a => (x.comp β) (b.ζ ^ e a h : oˣ) * x (v (idx a h))) := by
      funext a
      simp
    rw [hv]
    exact key
  refine ⟨σ, _, hemb, hproj, ideals_homogeneous.1 _ _ _ _ _ _ σ _ hLB, ?_, hsec⟩
  exact hcut K (x.comp β) t σ _ hemb fun h => hsec (hh h)

end GlobalTheory.ZM.GoodFibre
end
end

section

open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

theorem semiAbelian_model_determined_by_generic_fibre : ExtVStatement :=
  GlobalTheory.ModelUniqueChecks.extV_holds

end GlobalTheory
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
namespace GlobalTheory.ZM

theorem moduli_of_deeper_level : Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l l₂ : Level H), 1 ≤ D.p + D.q → l.Dvd l₂ → Nonempty (Moduli D l₂) → Nonempty (Moduli D l) := by
  intro L L2 hT E _ _ _ H D l l₂ hD hl ⟨Xo₂⟩
  obtain ⟨Q⟩ := GlobalTheory.T.nonempty_levelQuot_of_level_dvd L L2 hT E H D l l₂ Xo₂ hD hl
  exact ⟨{ X := Q.X, s := Q.s, qproj := Q.qproj, smooth := Q.smooth, univ := Q.univ,
           rep := GlobalTheory.T.levelQuotient_represents_reduced L L2 E H D l l₂ Xo₂ Q hD hl,
           unram := GlobalTheory.T.levelQuotient_unramified_dualNumberPoints L L2 E H D l l₂ Xo₂ Q hD hl }⟩
end GlobalTheory.ZM
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

theorem _root_.GlobalTheory.T.isHolTo_modulipoint_exp_of_holomorphic_periods : ThetaUnifAV → Out.Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)), 1 ≤ D.p + D.q → σ (baseKA l).ρ = H.rt0 → IsTypeFn H D.p D.q ty → ∀ (D' : Datum H) (t : D.La →ₗ[𝓞 E] D'.La) (m : ℕ) (B : Set (Fin m → ℂ)) (P : (Fin m → ℂ) → (D'.La →+ (Fin g → ℂ))) (y : (Fin m → ℂ) → (Sp ℂ ⟶ Xo.X)) (e : ∀ b, (Fin g → ℂ) → (Over.mk (y b) ⟶ Xo.univ.t.G)), (D'.p = D.p ∧ D'.q = D.q ∧ ∃ (f : ℕ → D.La →ₗ[𝓞 E] D'.La) (ν : ℕ → ℤ), (∀ n m : ℕ, 0 < n → 0 < m → ∀ a, ∃ e, f (n * m) a = f n a + n • e) ∧ (∀ n : ℕ, 0 < n → (∀ a, (∃ e, f n a = n • e) ↔ ∃ e, a = n • e) ∧ ∀ a', ∃ a e, a' = f n a + n • e) ∧ (∀ n : ℕ, 0 < n → ∀ a a', (n : ℤ) ∣ D'.EF (f n a) (f n a') - ν n * D.EF a a') ∧ σ (baseKA l).ζ = Complex.exp (-(2 * Real.pi * Complex.I) * (ν l.A : ℂ) / l.A) ∧ t = f l.M') → IsOpen B → IsHolPeriods D' ty B P → (∀ b ∈ B, ((y b) ≫ Xo.s = spMap σ ∧ IsPeriod D' ty (P b) ∧ ((∀ z w, (e b) (z + w) = (e b) z * (e b) w) ∧ Function.Surjective (e b) ∧ IsHolTo Set.univ (fun z => ((e b) z).left) ∧ (∀ w, ∃! v : epsPt (y b) ⟶ Xo.univ.t.G, IsDerivAt0 (fun z => ((e b) z).left) w v.left) ∧ (∀ v : epsPt (y b) ⟶ Xo.univ.t.G, spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = ((e b) 0).left → ∃! w, IsDerivAt0 (fun z => ((e b) z).left) w v.left)) ∧ (∀ z, (e b) z = 1 ↔ z ∈ ((P b)).range) ∧ (∀ (a : 𝓞 E) z, (e b) (fun k => ty k (a : E) * z k) = (e b) z ≫ Xo.univ.t.act.act a) ∧ (∀ (k : ℕ) (a a₂ : D'.La) (c : ℂˣ), 0 < k → (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (D'.EF a a₂ : ℂ) / k) → Out.WeilIs Xo.univ.t.G Xo.univ.t.PP.L k ((e b) ((k : ℂ)⁻¹ • (P b) a)) ((e b) ((k : ℂ)⁻¹ • (P b) a₂)) (unitOn c)) ∧ (∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La), toUnit _ ≫ Xo.univ.eta a = (e b) ((l.M : ℂ)⁻¹ • (P b) (t a))) ∧ ∀ a, toUnit _ ≫ Xo.univ.etaA a = (e b) ((l.A : ℂ)⁻¹ • (P b) (t a)))) → IsHolTo B y ∧ IsHolTo (B ×ˢ Set.univ) (fun bz : (Fin m → ℂ) × (Fin g → ℂ) => (e bz.1 bz.2).left) := by
  first | exact @GlobalTheory.isHolTo_point_and_exp_of_isHolPeriods | exact GlobalTheory.isHolTo_point_and_exp_of_isHolPeriods | (intros; apply GlobalTheory.isHolTo_point_and_exp_of_isHolPeriods <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

theorem _root_.GlobalTheory.T.exists_semiAbelianTriple_glue_common_genericPart : (∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (G G' : Over (Sp T)) [GrpObj G] [GrpObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ f : (Over.pullback (spMap (algebraMap T K))).obj G ⟶ (Over.pullback (spMap (algebraMap T K))).obj G', IsMonHom f → ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback (spMap (algebraMap T K))).map F = f) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X X₀ : Scheme.{0}) (j : X₀ ⟶ X) (t₀ : SAB H X₀) (I : Type) [Finite I] (U : I → X.Opens) (jU : ∀ i, X₀ ⟶ (U i).toScheme) (t : ∀ i, SAB H (U i).toScheme) (a : ∀ i, SABMap t₀ (t i) (jU i)), Nonempty I → (IsNormalScheme X ∧ ∃ z : X ⟶ Sp ℤ, LocallyOfFiniteType z ∧ Flat z) → IsPreimmersion j → Flat j → IsDominant j → QuasiCompact j → IsProper t₀.G.hom → ⨆ i, U i = ⊤ → (∀ i, jU i ≫ (U i).ι = j) → ∃ (t' : SAB H X) (a' : SABMap t₀ t' j) (n : ∀ i, SABMap (t i) t' (U i).ι), ∀ i, (a i).φ ≫ (n i).φ = a'.φ := by
  first | exact @GlobalTheory.exists_sab_glue_of_common_generic | exact GlobalTheory.exists_sab_glue_of_common_generic | (intros; apply GlobalTheory.exists_sab_glue_of_common_generic <;> assumption)
end
