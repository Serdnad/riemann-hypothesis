module

public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle006
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.TopAmpExists
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.DenseOfDenseP
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle009
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle106
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle122
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPrimitiveNormalisation
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle046
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSecImageNonzeroLocus
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaOfTranslDiff
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle003
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle002
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle104
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle005
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle166
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.AbelianVarietyCutOutBoundedDegreeTorsion
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle105
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle114
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsHomogeneousVolumeVeryAmpleProducts
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniversalFullLevelOfPelThetaFamily
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsAlternatingSkewNatural
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle090
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle034
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle167
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjIsAbelianSchemeDimRigidifiedSym
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PushEquivSymmLeft
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle019
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle020
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle081
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsMulEquivOfIsGrpPullback
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle026
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle109
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle157
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.FiniteOrderAutomorphismFixingLevelTrivialOnFixed
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

theorem _root_.GlobalTheory.T.exists_holomorphic_thetaConstants_polarisedLattices : Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ThetaUnifAV → ∀ (o : Type) [CommRing o] (g N' : ℕ) (J : Type) (b : TBase o (N' ^ 2)) (em : o →+* ℂ) (w w' : J) (La : Type) [AddCommGroup La] (EF : LinearMap.BilinForm ℤ La) (lam : Fin (2 * g) → La) (ac : J → La → La) (d : ℕ) (B : Set (Fin d → ℂ)) (Q : (Fin d → ℂ) → (La →+ (Fin g → ℂ))) (Hm : (Fin d → ℂ) → Matrix (Fin g) (Fin g) ℂ), Odd N' → Function.Bijective EF → IsOpen B → (∀ x, DifferentiableOn ℂ (fun bb => Q bb x) B) → (∀ bb ∈ B, (Function.Injective (Q bb) ∧ DiscreteTopology ((Q bb)).range ∧ Submodule.span ℝ (Set.range (Q bb)) = ⊤ ∧ ((Hm bb)).IsHermitian ∧ (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm (Hm bb) z z).re) ∧ ∀ x y, (hermForm (Hm bb) ((Q bb) x) ((Q bb) y)).im = EF x y) ∧ ∃ F : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ), ∀ x, F (Q bb x) = Q bb (ac w x)) → (∀ x, ac w x + ac w' x = x) → (∀ x y, EF (ac w x) y = EF x (ac w' y)) → ∃ θ : (Fin d → ℂ) → Ix g (N' ^ 2) → ℂ, (∀ a, DifferentiableOn ℂ (fun z => θ z a) B) ∧ ∀ bb ∈ B, ∀ t : TObj g (N' ^ 2) J b (spMap em), (∃ (u : HolUnif t.A t.L g) (χ' : u.Λ → ℂ), u.IsAH (Hm bb) χ' ∧ (∀ z, z ∈ u.Λ ↔ z ∈ ((Q bb)).range) ∧ (∀ x (l : u.Λ), (l : Fin g → ℂ) = (Q bb) x → χ' l = (-1) ^ EF x (ac w x)) ∧ (∀ i₀, (t.pt i₀).left = (u.ex (((N' ^ 2 : ℕ) : ℂ)⁻¹ • (Q bb) (lam i₀))).left) ∧ ∀ j₀, ∃ F : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ), (∀ x, F ((Q bb) x) = (Q bb) (ac j₀ x)) ∧ ∀ z, u.ex (F z) = u.ex z ≫ t.act j₀) → t.HasTh (𝟙 _) (θ bb) := by
  first | exact @GlobalTheory.exists_holomorphic_thetaConstants_of_family | exact GlobalTheory.exists_holomorphic_thetaConstants_of_family | (intros; apply GlobalTheory.exists_holomorphic_thetaConstants_of_family <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
open GlobalTheory.ZV

theorem _root_.GlobalTheory.T.abelianVariety_cut_out_bounded_degree_torsion : Out.Laws → Out.Laws2 → ∀ (g C : ℕ) (σ₀ : Type) [Finite σ₀] [Nonempty σ₀], ∃ d k₀ : ℕ, ∀ δ ≤ C ^ g, ∀ (σ : Type) [Finite σ] (r : σ → σ₀), Function.Surjective r → ∃ Q : Polynomial ℚ, ∀ (K : Type) [Field K] [IsAlgClosed K] (P : Out.PolAV (Sp K)), P.g = g → ∀ (Y : Scheme.{0}) (e : Y ≅ P.A.left) (M : LB Y) (th : σ → M.Sec) (k : ℕ) (Hh : Type) (y : Hh → (Out.baseOver (Sp K) ⟶ P.A)) (p : Hh → σ → K), M.IsLB → SymB (A := P.A) (M.pull e.inv) → VAmp (e.hom ≫ P.A.hom) M th → (∀ a a', r a = r a' → ∀ j, (th a).f j = (th a').f j) → (∀ n ≥ 1, SectionsHaveFiniteDimension (e.hom ≫ P.A.hom) (lbPow M n) (δ * n ^ g)) → k₀ ≤ k → (k : K) ≠ 0 → (∀ x : Out.baseOver (Sp K) ⟶ P.A, x ^ k = 1 → ∃ h, y h = x) → (∀ h, SecCoord M th ((y h).left ≫ e.inv) (p h)) → CutBy (idealOf (e.hom ≫ P.A.hom) M th (𝟙 Y)) Q d p := by
  first | exact @GlobalTheory.cutBy_idealOf_torsion | exact GlobalTheory.cutBy_idealOf_torsion | (intros; apply GlobalTheory.cutBy_idealOf_torsion <;> assumption)
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZV

namespace GlobalTheory.TwistIsTranslate

open CechPic

variable {K : Type} [Field K]

theorem pull_const {A T : Over (Sp K)} (x : 𝟙_ (Over (Sp K)) ⟶ A) (c : CechPic.Pic A.left) :
    CechPic.pull (toUnit T ≫ x).left c = 0 := by
  obtain ⟨L, hL, rfl⟩ := cls_surj c
  have hx : CechPic.pull x.left (cls L hL) = 0 := by
    have hc := hL.cover
    let z₀ : (𝟙_ (Over (Sp K))).left := (default : PrimeSpectrum K)
    have hz : x.left z₀ ∈ (⨆ i, L.U i) := by rw [hc]; trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hz
    refine GlobalTheory.RigidifyTwist.pull_cls_eq_zero hL x.left i fun z => ?_
    rwa [show z = z₀ from Subsingleton.elim (α := PrimeSpectrum K) _ _]
  rw [Over.comp_left, pull_comp, hx, map_zero]

theorem exists_comp_eq [IsAlgClosed K] {A B : Over (Sp K)} (s : A ⟶ B) [IsFinite s.left] [Surjective s.left]
    (y : 𝟙_ (Over (Sp K)) ⟶ B) : ∃ x : 𝟙_ (Over (Sp K)) ⟶ A, x ≫ s = y := by
  obtain ⟨t, ht⟩ := ReciprocityTheory.ChartRestriction.G.H1.SectionDivision.exists_section (k := K) (pullback.snd s.left y.left)
  have h1 := Over.w s
  have h2 := Over.w y
  refine ⟨Over.homMk (t ≫ pullback.fst s.left y.left) ?_, ?_⟩
  · simp only [Category.assoc, ← h1, pullback.condition_assoc, h2]
    simpa using ht
  · ext
    simp only [Over.comp_left, Over.homMk_left, Category.assoc, pullback.condition]
    rw [← Category.assoc, ht]
    exact Category.id_comp _

theorem lam_id_const {A : Over (Sp K)} [GrpObj A] [IsCommMonObj A] (x : 𝟙_ (Over (Sp K)) ⟶ A)
    (c : CechPic.Pic A.left) :
    lam c (𝟙 A) (toUnit A ≫ x) = CechPic.pull ((toUnit A ≫ x) * 𝟙 A).left c - c := by
  have h1 : (1 : A ⟶ A) = toUnit A ≫ (1 : 𝟙_ (Over (Sp K)) ⟶ A) := by simp
  have hc : (𝟙 A) * (toUnit A ≫ x) = (toUnit A ≫ x) * 𝟙 A := mul_comm _ _
  simp only [lam, hc, Over.id_left, pull_id, pull_const, h1]
  abel

theorem iso_of_formIs (P : Out.PolAV (Sp K)) (M : LB P.A.left) (hM : M.IsLB) (s : P.A ⟶ P.A) (hs : FormIs P M s)
    (x : 𝟙_ (Over (Sp K)) ⟶ P.A) :
    LBIso (LB.div M (LB.LinComb P.L (K := Fin 2) ![𝟙 P.A.left, ((toUnit P.A ≫ x ≫ s) * 𝟙 P.A).left] ![1, -1]))
      (M.pull ((toUnit P.A ≫ x) * 𝟙 P.A).left) := by
  obtain ⟨-, hiso⟩ := hs
  have hL : P.L.IsLB := P.isLB
  have hc1 : (cubeLB P.A ![fst P.A P.A, snd P.A P.A] M).IsLB := LB.isLB_linComb hM _ _
  have hc2 : (cubeLB P.A ![fst P.A P.A, snd P.A P.A ≫ s] P.L).IsLB := LB.isLB_linComb hL _ _
  have hLam : abelian₂ P.A M = cubeLB P.A ![fst P.A P.A, snd P.A P.A] M := rfl
  rw [hLam] at hiso
  have e := (cls_eq_iff hc1 hc2).2 hiso
  rw [cls_cube_two hM _ _ hc1, cls_cube_two hL _ _ hc2] at e
  have e2 := congrArg (CechPic.pull (lift (𝟙 P.A) (toUnit P.A ≫ x)).left) e
  rw [pull_lam, pull_lam] at e2
  simp only [lift_fst, lift_snd_assoc, lift_snd] at e2
  rw [lam_id_const, Category.assoc, lam_id_const] at e2
  have hd := LB.isLB_div hM (LB.isLB_linComb hL (K := Fin 2)
    ![𝟙 P.A.left, ((toUnit P.A ≫ x ≫ s) * 𝟙 P.A).left] ![1, -1])
  refine (cls_eq_iff hd (pull_isLB hM _)).1 ?_
  rw [cls_div hM (LB.isLB_linComb hL _ _), cls_linComb hL, cls_pull hM]
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, pull_id, one_smul,
    neg_smul]
  rw [sub_eq_iff_eq_add] at e2
  rw [e2]
  abel

theorem twist_iso_translate : Out.Laws → Out.Laws2 → ∀ (K : Type) [Field K] [IsAlgClosed K] (P : Out.PolAV (Sp K)) (M : LB P.A.left) (y : 𝟙_ (Over (Sp K)) ⟶ P.A), M.IsLB → Out.RelAmple P.A M → ∃ x : 𝟙_ (Over (Sp K)) ⟶ P.A, LBIso (LB.div M (LB.LinComb P.L (K := Fin 2) ![𝟙 P.A.left, ((toUnit P.A ≫ y) * 𝟙 P.A).left] ![1, -1])) (M.pull ((toUnit P.A ≫ x) * 𝟙 P.A).left) := by
  intro hA hB K _ _ P M y hM hAmp
  obtain ⟨s, hs⟩ := GlobalTheory.T.exists_polarisationForm_of_lineBundle hA hB K P M hM
  obtain ⟨hfin, hsurj⟩ := GlobalTheory.T.isFinite_and_surjective_of_formIs' hA hB K P M s hM hAmp hs
  obtain ⟨x, hx⟩ := exists_comp_eq s y
  refine ⟨x, ?_⟩
  have h := iso_of_formIs P M hM s hs x
  rwa [hx] at h

end GlobalTheory.TwistIsTranslate
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZV

theorem _root_.GlobalTheory.T.exists_homogeneous_volume_veryAmple_products : Out.Laws → Out.Laws2 → ∀ (K : Type) [Field K] [IsAlgClosed K] (P : Out.PolAV (Sp K)) (I : Type) [Fintype I] (φ : I → (P.A.left ⟶ P.A.left)) (r : ℕ) (ε : Fin r → I → ℤ), 1 ≤ r → (∀ k, ∃ (m : ℕ) (th : Fin (m + 1) → (LB.LinComb P.L φ (ε k)).Sec), VAmp P.A.hom _ th) → ∃ Φ : MvPolynomial (Fin r) ℚ, Φ.IsHomogeneous P.g ∧ ∀ n : Fin r → ℕ, (∀ k, 1 ≤ n k) → Vol P.A.hom (LB.LinComb P.L φ (fun i => ∑ k, (n k : ℤ) * ε k i)) P.g ((MvPolynomial.eval (fun k => (n k : ℚ)) Φ : ℚ) : ℝ) := by
  first | exact @GlobalTheory.VolPoly.exists_homogeneous_vol | exact GlobalTheory.VolPoly.exists_homogeneous_vol | (intros; apply GlobalTheory.VolPoly.exists_homogeneous_vol <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ZM

theorem _root_.GlobalTheory.T.exists_universal_fullLevel_of_pelThetaFamily : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (n N' : ℕ) (g : ℕ) (J : Type) [Finite J] (a : J → 𝓞 E) (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] D.La) (b : TBase (RZ H n (N' ^ 2)) (N' ^ 2)) (F : ThetaFam n (RZ H n (N' ^ 2)).subtype (PELClass (b := b) D a bas (RZ.rt H n (N' ^ 2)) (RZ H n (N' ^ 2)).subtype)) (τ : SAB H F.MM), IsSympBasis D bas → Subring.closure (Set.range a) = ⊤ → (∃ w w', a w = H.w0 ∧ a w' = H.bar H.w0) → (b.ζ : RZ H n (N' ^ 2)) = RZ.ze H n (N' ^ 2) → IsPEL D a bas (RZ.rt H n (N' ^ 2)) F.univ τ → SmoothOfRelativeDimension D.dim (pullback.snd F.s (spMap (algebraMap (RZ H n (N' ^ 2)) (FractionRing (RZ H n (N' ^ 2)))))) → 1 ≤ D.p + D.q → n.Prime → Odd n → (∃ j, 1 ≤ j ∧ N' = n ^ j) → ∃ lev : D.La → (𝟙_ (Over F.MM) ⟶ τ.G), FamCore D F.s τ lev := by
  first | exact @GlobalTheory.exists_famCore_of_thetaFam | exact GlobalTheory.exists_famCore_of_thetaFam | (intros; apply GlobalTheory.exists_famCore_of_thetaFam <;> assumption)
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ZM

namespace GlobalTheory.FullSpread

section Pairing

variable {S : Scheme.{0}} [IsLocallyNoetherian S] (P : Out.PolAV S) {T : Over S}

theorem weilIs_pow_left (hW : Out.WeilSt) {n : ℕ} {x y : T ⟶ P.A} {c : Γ(T.left, ⊤)ˣ}
    (h : Out.WeilIs P.A P.L n x y c) (m : ℕ) : Out.WeilIs P.A P.L n (x ^ (m + 1)) y (c ^ (m + 1)) := by
  induction m with
  | zero => rwa [zero_add, pow_one, pow_one]
  | succ m ih =>
    rw [pow_succ x, pow_succ c]
    exact (hW S P n T).2.1 _ _ _ _ _ ih h

theorem weilIs_lower (hW : Out.WeilSt) {n m : ℕ} (hm : 0 < m) (hu : IsUnit ((n * m : ℕ) : Γ(T.left, ⊤)))
    {x y : T ⟶ P.A} {c : Γ(T.left, ⊤)ˣ} (hx : x ^ (n * m) = 1) (hy : y ^ (n * m) = 1)
    (h : Out.WeilIs P.A P.L ((n * m : ℕ) : ℤ) x y c) : Out.WeilIs P.A P.L n (x ^ m) (y ^ m) (c ^ m) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm.ne'
  have h₁ := CommPairing.weilIs_symm P.isLB (weilIs_pow_left P hW (CommPairing.weilIs_symm P.isLB h) m)
  rw [inv_pow, inv_inv, Nat.cast_mul] at h₁
  exact ((hW S P n T).2.2.2 _ x _ _ hu hx (by rw [← pow_mul, mul_comm, hy])).1 h₁

theorem eq_one_of_weilIs_one {K : Type} [Field K] (hW : Out.WeilSt) {x : Sp K ⟶ S} {n : ℕ}
    {y : Over.mk x ⟶ P.A} {c : Kˣ} (h : Out.WeilIs P.A P.L n 1 y (unitOn c)) : c = 1 := by
  have h₁ := (hW S P n _).2.1 _ _ _ _ _ h h
  rw [_root_.mul_one] at h₁
  have e : unitOn (c * c) = unitOn c * unitOn c := map_mul _ _ _
  exact mul_eq_left.1 (weilIs_unique_fieldPoint S P.A P.L P.isLB K x n 1 y _ _ (e ▸ h₁) h)

end Pairing

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {n N : ℕ}

theorem rt_sq (H : Host E) (n N : ℕ) : RZ.rt H n N ^ 2 = -(H.d : RZ H n N) := by
  apply Subtype.ext
  have e : ((RZ.rt H n N : RZ H n N) : ℂ) = H.rt0 := by
    change 2 * ((1 + H.rt0) / 2) - 1 = H.rt0
    ring
  simp [e, H.sqrt_neg_disc_sq]

def GeomAt (D : Datum H) {S : Scheme.{0}} (t : SAB H S) (lev : D.La → (𝟙_ (Over S) ⟶ t.G)) {k : Type} [Field k]
    (x : Sp k ⟶ S) (β : RZ H n N →+* k) : Prop :=
  DetCond D t.act x (β (RZ.rt H n N)) ∧
    ∃ I : TateIso D k (Over.mk x ⟶ t.G) (fun a g => g ≫ t.act.act a)
        (fun m g g' c => Out.WeilIs t.G t.PP.L m g g' (unitOn c)),
      (I.ζ N : k) = β (RZ.ze H n N) ∧ ∀ a, toUnit _ ≫ lev a = I.ev N a

theorem GeomAt.push {S S' : Scheme.{0}} {t : SAB H S} {t' : SAB H S'} {f : S' ⟶ S} (ν : SABMap t' t f)
    {lev : D.La → (𝟙_ (Over S) ⟶ t.G)} {lev' : D.La → (𝟙_ (Over S') ⟶ t'.G)}
    (hl : ∀ a, (lev' a).left ≫ ν.φ = f ≫ (lev a).left) {k : Type} [Field k] {y : Sp k ⟶ S'} {β : RZ H n N →+* k}
    (h : GeomAt D t' lev' y β) : GeomAt D t lev (y ≫ f) β := by
  obtain ⟨hdet, I, hI, hA⟩ := h
  have hL : LBIso t'.PP.L (t.PP.L.pull ν.cm.F) := by
    obtain ⟨w, hw, -⟩ := ν.lin
    exact ⟨w, hw⟩
  refine ⟨(detCond_iff_of_sabMap E H D S S' t t' f ⟨ν⟩ k y _).1 hdet,
    ObjPull.tateMove (ObjPull.pushEquiv ν.cart (Over.mk y)).symm (fun c g => ?_) (fun m g g' c hc => ?_) I,
    hI, fun a => ?_⟩
  · obtain ⟨g, rfl⟩ := (ObjPull.pushEquiv ν.cart (Over.mk y)).surjective g
    rw [MulEquiv.symm_apply_apply, MulEquiv.symm_apply_eq]
    apply Over.OverMorphism.ext
    show (g.left ≫ _) ≫ _ = (g.left ≫ _) ≫ _
    rw [Category.assoc, ← ν.act, Category.assoc]
  · exact (weilIs_iff_of_isGrpPullback_comm S S' t.G t'.G f ν.cm.F t.PP.L t'.PP.L t.PP.isLB t'.PP.isLB ν.cart hL
      (Over.mk y) m _ _ g g' _ (ObjPull.pushEquiv_symm_left ν.cart (Over.mk y) g).symm
      (ObjPull.pushEquiv_symm_left ν.cart (Over.mk y) g').symm).1 hc
  · apply Over.OverMorphism.ext
    show _ = (I.ev N a).left ≫ ν.φ
    rw [← hA, Over.comp_left, Over.comp_left, ObjPull.toUnit_left', ObjPull.toUnit_left', Category.assoc, hl]
    exact Category.assoc _ _ _

theorem geomAt_of_dense (hL : Out.Laws) {S : Scheme.{0}} [IsLocallyNoetherian S] [IsReduced S] [ConnectedSpace S]
    (s : S ⟶ Sp (RZ H n N)) (t : SAB H S) (lev : D.La → (𝟙_ (Over S) ⟶ t.G)) (hN : 0 < N)
    (hp : IsProper t.G.hom) (ha : Out.RelAmple t.G t.PP.L) (hk : Out.KTriv t.G t.PP.L)
    (hd : Dense {p : S | ∃ (K : Type) (_ : Field K) (_ : IsAlgClosed K) (_ : CharZero K) (x : Sp K ⟶ S)
      (β : RZ H n N →+* K), p ∈ Set.range x ∧ x ≫ s = spMap β ∧ GeomAt D t lev x β})
    (K : Type) [Field K] [IsAlgClosed K] [CharZero K] (x : Sp K ⟶ S) (β : RZ H n N →+* K) (hx : x ≫ s = spMap β) :
    GeomAt D t lev x β := by
  have := t.semi.smooth
  have := t.semi.geomConnected
  have : ConnectedSpace t.G.left := GeometricallyConnected.connectedSpace t.G.hom t.G.hom.isOpenMap
  obtain ⟨g, hg⟩ := exists_dim_of_preconnected t.G.hom (Classical.arbitrary _)
  let P : Out.PolAV S :=
    { A := t.G, g := g, smoothDim := hg, L := t.PP.L, isLB := t.PP.isLB, ample := ha, ktriv := hk
      isAb := ⟨t.semi.comm, t.semi.smooth, hp, t.semi.geomConnected⟩
      rigid := ObjDim.rigidified
      sym := ObjDim.sym }
  have hdet : DetCond D t.act x (β (RZ.rt H n N)) :=
    GlobalTheory.T.determinantCondition_spreads_of_dense_points E H D S t.G g t.act _ s _ hg (rt_sq H n N) (hd.mono fun p hp => by
      obtain ⟨K, _, _, _, x, β, h₁, h₂, h₃, -⟩ := hp
      exact ⟨K, inferInstance, inferInstance, inferInstance, x, β, h₁, h₂, h₃⟩) K x β hx
  refine ⟨hdet, ?_⟩
  have hdim : g = Module.finrank ℚ E / 2 * (D.p + D.q) :=
    ObjDim.dim_eq_of_detCond D t.act x (by rw [← map_pow, rt_sq, map_neg, map_natCast]) hdet
      ((smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback (IsPullback.of_hasPullback t.G.hom x) hg)
  have e₀ : ∀ {K : Type} [Field K] (x : Sp K ⟶ S),
      (Over.homMk x (by simp) : Over.mk x ⟶ Out.baseOver S) = toUnit (Over.mk x) := fun x =>
    Over.OverMorphism.ext (ObjPull.toUnit_left' (Over.mk x)).symm
  have hcard : ∀ m, 0 < m → Nat.card {z : Over.mk x ⟶ t.G // z ^ m = 1} = m ^ Module.finrank ℤ D.La := fun m hm => by
    rw [finrank_int_lattice D, ← hdim]
    exact (hL.mulN S P m hm).2.2.2.2 K x (Nat.cast_ne_zero.2 hm.ne')
  obtain ⟨I, hI, hA⟩ := GlobalTheory.TateTower.tateIso_of_levels E H D K (Over.mk x ⟶ t.G) (fun c z => z ≫ t.act.act c)
    (fun n z z' c => Out.WeilIs t.G t.PP.L n z z' (unitOn c)) N (β (RZ.ze H n N)) _ id
    (fun i => toUnit _ ≫ lev i) hN
    (fun n hn => Nat.finite_of_card_ne_zero (by rw [hcard n hn]; positivity))
    (fun n m z z' c hn hm hz hz' h => by
      have e : unitOn (c ^ m) = unitOn c ^ m := map_pow _ _ _
      have u : IsUnit ((n * m : ℕ) : K) := (Nat.cast_ne_zero.2 (Nat.mul_pos hn hm).ne').isUnit
      have u' := u.map (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom
      rw [map_natCast] at u'
      rw [e]
      exact weilIs_lower P hL.weil hm u' hz hz' h)
    (fun m hm => by
      have hn := Nat.mul_pos hN hm
      obtain ⟨ζ, ev, h₁, h₂, h₃, h₄, h₅, h₆, h₇⟩ := GlobalTheory.T.exists_level_isometry_of_dense_geometric_points hL E H D S P t.act.act _ s (RZ.ze H n N) _
        id lev (N * m) m hn (hd.mono fun p hp => by
          obtain ⟨K, _, _, _, x, β, h₁, h₂, -, I, h₃, h₄⟩ := hp
          exact ⟨K, inferInstance, x, β, I.ζ (N * m), I.ev (N * m), Nat.cast_ne_zero.2 hn.ne', h₁, h₂, I.ζ_prim _ hn,
            I.add _, fun v => (I.onto _ hn _).2 ⟨v, rfl⟩, I.lin _, I.isom _ hn,
            by rw [← h₃, ← I.ζ_pow N m hN hm, Units.val_pow_eq_pow_val],
            fun i => (I.tower N m hN hm _).trans ((h₄ i).symm.trans (congrArg (· ≫ lev i) (e₀ x).symm))⟩)
          K x β (Nat.cast_ne_zero.2 hn.ne') hx
      obtain ⟨h₈, h₉⟩ := GlobalTheory.T.torsionIsometry_primitiveRoot_bijective_mod_n E H D K (Over.mk x ⟶ t.G)
        (fun z z' c => Out.WeilIs t.G t.PP.L (N * m : ℕ) z z' (unitOn c)) (N * m) ζ ev hn (hcard _ hn)
        (fun _ _ _ h => eq_one_of_weilIs_one P hL.weil h) h₁ h₂ h₃ h₅
      exact ⟨ζ, ev, h₁, h₂, h₄, h₈, h₉, h₅, h₆, fun i => (h₇ i).trans (congrArg (· ≫ lev i) (e₀ x))⟩)
  exact ⟨I, hI, fun a => (hA a).symm⟩

theorem fullObj_of_genericFibre : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (n N : ℕ) (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K] (s : Sp V ⟶ Sp (RZ H n N)) (t : SAB H (Sp V)) (lv : D.La → (𝟙_ (Over (Sp V)) ⟶ t.G)) (tK : SAB H (Sp K)) (ν : SABMap tK t (spMap (algebraMap V K))) (lvK : D.La → (𝟙_ (Over (Sp K)) ⟶ tK.G)), 0 < N → IsProper t.G.hom → Out.RelAmple t.G t.PP.L → Out.KTriv t.G t.PP.L → (∀ a c, lv (a + c) = lv a * lv c) → (∀ a, lv (N • a) = 1) → (∀ a, (lvK a).left ≫ ν.φ = spMap (algebraMap V K) ≫ (lv a).left) → FullObj D (spMap (algebraMap V K) ≫ s) tK lvK → FullObj D s t lv := by
  intro hL _ E _ _ _ H D n N V K _ _ _ _ _ _ s t lv tK ν lvK hN hp ha hk hadd hker hl o
  refine ⟨hp, ha, hk, hadd, hker, fun k _ _ _ x β hx => ?_⟩
  have : CharZero V := (Spec.preimage x).hom.charZero
  have : CharZero K := charZero_of_injective_algebraMap (IsFractionRing.injective V K)
  let Ω := AlgebraicClosure K
  let y : Sp Ω ⟶ Sp K := spMap (algebraMap K Ω)
  obtain ⟨b, hb⟩ : ∃ b : RZ H n N →+* Ω, y ≫ spMap (algebraMap V K) ≫ s = spMap b :=
    ⟨(Spec.preimage (y ≫ spMap (algebraMap V K) ≫ s)).hom, (Spec.map_preimage _).symm⟩
  have hΩ : GeomAt D t lv (y ≫ spMap (algebraMap V K)) b := GeomAt.push ν hl (o.geom Ω y b hb)
  have hdense : Dense {(⊥ : PrimeSpectrum V)} := by
    rw [dense_iff_closure_eq, PrimeSpectrum.closure_singleton]
    simp
  refine geomAt_of_dense hL s t lv hN hp ha hk (Dense.mono ?_ hdense) k x β hx
  rintro _ rfl
  refine ⟨Ω, inferInstance, inferInstance, inferInstance, _, b, ⟨(⊥ : PrimeSpectrum Ω), ?_⟩,
    (Category.assoc _ _ _).trans hb, hΩ⟩
  apply PrimeSpectrum.ext
  show Ideal.comap (algebraMap V K) (Ideal.comap (algebraMap K Ω) ⊥) = ⊥
  rw [Ideal.comap_bot_of_injective _ (algebraMap K Ω).injective,
    Ideal.comap_bot_of_injective _ (IsFractionRing.injective V K)]

end GlobalTheory.FullSpread
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
open GlobalTheory.ZM.NearBuild

namespace GlobalTheory.ZM.NearBuild

theorem torsBasis_pow {G : Type} [CommGroup G] {r k l : ℕ} (hk : k ≠ 0) (hl : l ≠ 0) (y : Fin r → G)
    (hy : ∀ i, y i ^ (k * l) = 1)
    (h : ∀ z : G, z ^ (k * l) = 1 → ∃! c : Fin r → ZMod (k * l), ∏ i, y i ^ (c i).val = z)
    (z : G) (hz : z ^ k = 1) : ∃! c : Fin r → ZMod k, ∏ i, (y i ^ l) ^ (c i).val = z := by
  haveI : NeZero k := ⟨hk⟩
  have red : ∀ e : Fin r → ℕ, ∏ i, y i ^ ((e i : ZMod (k * l))).val = ∏ i, y i ^ e i := fun e =>
    Finset.prod_congr rfl fun i _ => by rw [ZMod.val_natCast, ← pow_eq_pow_mod _ (hy i)]
  have tor : ∀ e : Fin r → ℕ, (∏ i, y i ^ e i) ^ (k * l) = 1 := fun e => by
    rw [← Finset.prod_pow]
    exact Finset.prod_eq_one fun i _ => by rw [← pow_mul, mul_comm, pow_mul, hy, one_pow]
  have inj : ∀ e e' : Fin r → ℕ, ∏ i, y i ^ e i = ∏ i, y i ^ e' i → ∀ i, e i ≡ e' i [MOD k * l] := by
    intro e e' he i
    have := (h _ (tor e)).unique (y₁ := fun i => (e i : ZMod (k * l))) (y₂ := fun i => (e' i : ZMod (k * l)))
      (red e) ((red e').trans he.symm)
    exact (ZMod.natCast_eq_natCast_iff _ _ _).1 (congrFun this i)
  obtain ⟨c, hc, -⟩ := h z (by rw [pow_mul, hz, one_pow])
  have hd : ∀ i, l ∣ (c i).val := fun i => by
    have := inj (fun i => k * (c i).val) (fun _ => 0) (by
      simp only [pow_zero, Finset.prod_const_one]
      rw [← hz, ← hc, ← Finset.prod_pow]
      exact Finset.prod_congr rfl fun i _ => by rw [← pow_mul, mul_comm]) i
    exact Nat.dvd_of_mul_dvd_mul_left (Nat.pos_of_ne_zero hk) ((Nat.modEq_zero_iff_dvd).1 this)
  choose d hd using hd
  refine ⟨fun i => (d i : ZMod k), ?_, fun c' hc' => funext fun i => ?_⟩
  · rw [← hc]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [ZMod.val_natCast, ← pow_eq_pow_mod _ (by rw [← pow_mul, mul_comm, hy]), hd, pow_mul]
  · have := inj (fun i => l * (c' i).val) (fun i => l * d i) (by
      simp only [pow_mul, ← hd]
      rw [hc, ← hc']) i
    rw [mul_comm k l] at this
    have h2 := Nat.ModEq.mul_left_cancel' hl this
    rw [← (ZMod.natCast_eq_natCast_iff _ _ _).2 h2, ZMod.natCast_zmod_val]

variable {S : Scheme.{0}}

theorem torsBasis_pow_linComb {A T : Over S} [GrpObj A] [IsCommMonObj A] {r k l N : ℕ} (hN : N = k * l) (hN0 : N ≠ 0)
    (u : T ⟶ Out.baseOver S) (y : Fin r → (Out.baseOver S ⟶ A)) (hy : ∀ i, y i ^ N = 1)
    (h : ∀ z : T ⟶ A, z ^ N = 1 → ∃! c : Fin r → ZMod N, Out.linComb (fun i => u ≫ y i) (fun i => (c i).val) = z)
    (z : T ⟶ A) (hz : z ^ k = 1) :
    ∃! c : Fin r → ZMod k, Out.linComb (fun i => u ≫ y i ^ l) (fun i => (c i).val) = z := by
  subst hN
  simp only [Out.linComb, List.prod_ofFn, MonObj.comp_pow] at h ⊢
  exact torsBasis_pow (left_ne_zero_of_mul hN0) (right_ne_zero_of_mul hN0) _
    (fun i => by rw [← MonObj.comp_pow, hy, MonObj.comp_one]) h z hz

theorem exists_polFam_of_grpFam : Out.Laws → Out.Laws2 → ∀ (o : Type) [CommRing o] (g N' : ℕ) (J : Type) (b : TBase o (N' ^ 2)) (Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) (κ : ℕ) (R : Type) [CommRing R] [IsNoetherianRing R] [IsReduced R] (β : o →+* R) (v : Ix g (N' ^ 2) → R) (m : ℕ) (A : Over (Sp R)) [GrpObj A] (L : LB A.left) (act : J → (A ⟶ A)) (Q : Fin (2 * g) → (Out.baseOver (Sp R) ⟶ A)), N' ≠ 0 → Odd m → m ∣ N' → DenseP (objPrimes b Mat κ β v) → GrpFam b Mat κ β v m A L act Q → ∃ L' : LB A.left, PolFam b Mat κ β v A L' act Q := by
  intro hL hL2 o _ g N' J b Mat κ R _ _ _ β v m A _ L act Q hN0 hodd ⟨l, hl⟩ hD ⟨hab, hsm, hlb, hamp, hlab, hfib⟩
  have hun : IsUnit (m : R) := by
    have := b.unit.map β
    rw [map_natCast, Nat.cast_pow, isUnit_pow_iff two_ne_zero, hl, Nat.cast_mul] at this
    exact isUnit_of_mul_isUnit_left this
  have := hab.comm
  obtain ⟨L', l1, l2, l3, l4, l5⟩ := GlobalTheory.OddDescent.exists_descended hL hL2 R A g m L
    (fun i => (Q i ^ l : Out.baseOver (Sp R) ⟶ A)) hab hsm hodd hun hlb hamp
    (fun i => by
      have e : l * m = N' := by rw [mul_comm, ← hl]
      have : (Q i ^ l) ^ m = 1 := by rw [← pow_mul, e, hlab.2.1]
      exact this)
    (fun K _ _ x => torsBasis_pow_linComb hl hN0 _ _ hlab.2.1 (hlab.2.2 K x))
    (fun r hr => hD r fun q hq hqp => hr q (by
      obtain ⟨K, _, _, x, s, t, hx, ht⟩ := mem_objPrimes.1 hq
      obtain ⟨ψ, hψ, hi⟩ := hfib K x s t ht
      exact ⟨K, inferInstance, inferInstance, x, t.pol, ψ, hx, hψ.1, hi⟩) hqp)
  refine ⟨L', hab, hsm, l1, l2, l3, l4, hlab, fun K _ _ x s t ht => ?_⟩
  obtain ⟨ψ, hψ, hi⟩ := hfib K x s t ht
  exact ⟨ψ, hψ, l5 K x t.pol ψ hψ.1 hi⟩

end GlobalTheory.ZM.NearBuild
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.Moduli

theorem exists_point_of_isPeriod : ThetaUnifAV → Out.Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)), 1 ≤ D.p + D.q → σ (baseKA l).ρ = H.rt0 → IsTypeFn H D.p D.q ty → ∀ (D' : Datum H) (t : D.La →ₗ[𝓞 E] D'.La) (P : D'.La →+ (Fin g → ℂ)), (D'.p = D.p ∧ D'.q = D.q ∧ ∃ (f : ℕ → D.La →ₗ[𝓞 E] D'.La) (ν : ℕ → ℤ), (∀ n m : ℕ, 0 < n → 0 < m → ∀ a, ∃ e, f (n * m) a = f n a + n • e) ∧ (∀ n : ℕ, 0 < n → (∀ a, (∃ e, f n a = n • e) ↔ ∃ e, a = n • e) ∧ ∀ a', ∃ a e, a' = f n a + n • e) ∧ (∀ n : ℕ, 0 < n → ∀ a a', (n : ℤ) ∣ D'.EF (f n a) (f n a') - ν n * D.EF a a') ∧ σ (baseKA l).ζ = Complex.exp (-(2 * Real.pi * Complex.I) * (ν l.A : ℂ) / l.A) ∧ t = f l.M') → IsPeriod D' ty P → ∃ (y : Sp ℂ ⟶ Xo.X) (e : (Fin g → ℂ) → (Over.mk y ⟶ Xo.univ.t.G)), (y ≫ Xo.s = spMap σ ∧ IsPeriod D' ty P ∧ ((∀ z w, e (z + w) = e z * e w) ∧ Function.Surjective e ∧ IsHolTo Set.univ (fun z => (e z).left) ∧ (∀ w, ∃! v : epsPt y ⟶ Xo.univ.t.G, IsDerivAt0 (fun z => (e z).left) w v.left) ∧ (∀ v : epsPt y ⟶ Xo.univ.t.G, spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = (e 0).left → ∃! w, IsDerivAt0 (fun z => (e z).left) w v.left)) ∧ (∀ z, e z = 1 ↔ z ∈ (P).range) ∧ (∀ (a : 𝓞 E) z, e (fun k => ty k (a : E) * z k) = e z ≫ Xo.univ.t.act.act a) ∧ (∀ (k : ℕ) (a a₂ : D'.La) (c : ℂˣ), 0 < k → (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (D'.EF a a₂ : ℂ) / k) → Out.WeilIs Xo.univ.t.G Xo.univ.t.PP.L k (e ((k : ℂ)⁻¹ • P a)) (e ((k : ℂ)⁻¹ • P a₂)) (unitOn c)) ∧ (∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La), toUnit _ ≫ Xo.univ.eta a = e ((l.M : ℂ)⁻¹ • P (t a))) ∧ ∀ a, toUnit _ ≫ Xo.univ.etaA a = e ((l.A : ℂ)⁻¹ • P (t a))) := by
  intro hT hL
  have hG : Out.GlobalFnsSt := hL.globalFns
  exact GlobalTheory.exists_point_of_period hT hL GlobalTheory.Moduli.cube_of_isLB GlobalTheory.principalTorus_algebraic
    (GlobalTheory.exists_isMonHom_of_map_lattice hT hL) (GlobalTheory.T.lambdaBundle_adjoint_of_weilPairing_adjoint hL)
    (GlobalTheory.PrimNorm.exists_primitive_normalisation hG) (GlobalTheory.kTriv_of_descent hL)
    GlobalTheory.relAmple_finite_pow_iso (GlobalTheory.moduli_rep_of_base GlobalTheory.ObjMaps.id_comp_cancel)

end GlobalTheory.Moduli
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

theorem _root_.GlobalTheory.T.finiteOrderAutomorphism_fixing_level_trivial_on_fixedFibre : Out.Laws → Out.Laws2 → Out.Laws3 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (S : ℕ) (β : RZ H S l.A →+* KA l) (C : Cpt Xo.s Xo.univ.t β) (r : Xo.X ≅ Xo.X) (ν : SABMap Xo.univ.t Xo.univ.t r.hom) (ρ : C.X ≅ C.X) (mu : SABMap C.t C.t ρ.hom), IsInc (RZ H S l.A).subtype (KA l).val.toRingHom β → 0 < S → (∃ e, l.A ∣ S ^ e) → C.j ≫ ρ.hom = r.hom ≫ C.j → C.m.φ ≫ mu.φ = ν.φ ≫ C.m.φ → l.M ∣ S → r.hom ≫ Xo.s = Xo.s → (∀ x, (Xo.univ.eta x).left ≫ ν.φ = r.hom ≫ (Xo.univ.eta x).left) → (∃ (τ : Aut C.t.G.left) (d : ℕ), 0 < d ∧ τ ^ d = 1 ∧ τ.asIso.hom = mu.φ) → ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ C.X), x ≫ ρ.hom = x → pullback.fst C.t.G.hom x ≫ mu.φ = pullback.fst C.t.G.hom x := by
  first | exact @GlobalTheory.fibre_fixed_of_finite_order_of_level_fixed | exact GlobalTheory.fibre_fixed_of_finite_order_of_level_fixed | (intros; apply GlobalTheory.fibre_fixed_of_finite_order_of_level_fixed <;> assumption)
end
