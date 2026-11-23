module

public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle002
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle005
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle033
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle122
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsClosedTriv
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle160
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle088
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle109
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle077
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle009
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle017
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle112
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LbIsoCubeLBOfWeilIsAdjoint
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle159
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.IsIntegralOfIsAbelianSchemeField
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle018
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle090
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LocGenOfTrivial
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle007
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZV

noncomputable section
namespace GlobalTheory.BundleForm

section
variable {Pic : Scheme.{0} → Type 1} [∀ X, CommGroup (Pic X)]
  (pl : ∀ {X Y : Scheme.{0}}, (Y ⟶ X) → (Pic X →* Pic Y))
  {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A]

def lam (c : Pic A.left) {T : Over S} (a b : T ⟶ A) : Pic T.left :=
  pl (a * b).left c * pl (1 : T ⟶ A).left c / (pl a.left c * pl b.left c)

theorem lam_one_left (c : Pic A.left) {T : Over S} (b : T ⟶ A) : lam @pl c 1 b = 1 := by
  simp [lam, _root_.mul_comm]

theorem lam_one_right (c : Pic A.left) {T : Over S} (a : T ⟶ A) : lam @pl c a 1 = 1 := by
  simp [lam]

theorem lam_comm (c : Pic A.left) {T : Over S} (a b : T ⟶ A) : lam @pl c a b = lam @pl c b a := by
  unfold lam
  rw [_root_.mul_comm a b, _root_.mul_comm (pl a.left c)]

theorem pl_lam (hc : ∀ (X Y Z : Scheme.{0}) (f : Y ⟶ X) (g : Z ⟶ Y) (c : Pic X), pl (g ≫ f) c = pl g (pl f c))
    (c : Pic A.left) {T T' : Over S} (u : T' ⟶ T) (a b : T ⟶ A) :
    pl u.left (lam @pl c a b) = lam @pl c (u ≫ a) (u ≫ b) := by
  unfold lam
  rw [map_div, map_mul, map_mul, ← hc, ← hc, ← hc, ← hc, ← MonObj.comp_mul, ← MonObj.comp_one u]
  rfl

theorem cl_cube (cl : ∀ {X : Scheme.{0}}, LB X → Pic X)
    (hl : ∀ (X Y : Scheme.{0}) (L : LB X), L.IsLB → ∀ (I : Type) [Fintype I] (φ : I → (Y ⟶ X)) (ε : I → ℤ),
      (LB.LinComb L φ ε).IsLB ∧ cl (LB.LinComb L φ ε) = ∏ k, pl (φ k) (cl L) ^ ε k)
    {L : LB A.left} (hL : L.IsLB) {T : Over S} (a b : T ⟶ A) :
    cl (cubeLB A ![a, b] L) = lam @pl (cl L) a b := by
  unfold cubeLB
  rw [(hl _ _ L hL _ _ _).2, ← Equiv.ulift.symm.prod_comp]
  have e : (Finset.univ : Finset (Finset (Fin 2))) = {∅, {0}, {1}, {0, 1}} := by decide
  rw [e, Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_insert (by decide),
    Finset.prod_singleton]
  have e0 : psum A ![a, b] ∅ = 1 := rfl
  have e1 : psum A ![a, b] {0} = a := _root_.mul_one a
  have e2 : psum A ![a, b] {1} = b := _root_.mul_one b
  have e3 : psum A ![a, b] {0, 1} = a * b := congrArg (a * ·) (_root_.mul_one b)
  simp only [Equiv.ulift_symm_down, e0, e1, e2, e3, lam]
  simp [div_eq_mul_inv, _root_.mul_comm, _root_.mul_left_comm, _root_.mul_assoc]

theorem eq_of_lam_eq (cl : ∀ {X : Scheme.{0}}, LB X → Pic X)
    (h1 : ∀ (X : Scheme.{0}) (L : LB X), L.IsLB → (cl L = 1 ↔ ∃ t : LB.Gen L, t.IsGen))
    (hc : ∀ (X Y Z : Scheme.{0}) (f : Y ⟶ X) (g : Z ⟶ Y) (c : Pic X), pl (g ≫ f) c = pl g (pl f c))
    (hl : ∀ (X Y : Scheme.{0}) (L : LB X), L.IsLB → ∀ (I : Type) [Fintype I] (φ : I → (Y ⟶ X)) (ε : I → ℤ),
      (LB.LinComb L φ ε).IsLB ∧ cl (LB.LinComb L φ ε) = ∏ k, pl (φ k) (cl L) ^ ε k)
    {L : LB A.left} (hL : L.IsLB) (hK : Out.KTriv A L) {T : Over S} (y y' : T ⟶ A)
    (h : lam @pl (cl L) (fst T A ≫ y) (snd T A) = lam @pl (cl L) (fst T A ≫ y') (snd T A)) : y = y' := by
  let τ : T ⊗ A ⟶ T ⊗ A := lift (fst T A) ((fst T A ≫ y')⁻¹ * snd T A)
  have h' := congrArg (pl τ.left) h
  rw [pl_lam @pl hc, pl_lam @pl hc, ← Category.assoc, ← Category.assoc, lift_fst, lift_snd] at h'
  have et : Out.translPt A (y * y'⁻¹) = (fst T A ≫ y) * ((fst T A ≫ y')⁻¹ * snd T A) := by
    change (fst T A ≫ (y * y'⁻¹)) * snd T A = _
    rw [MonObj.comp_mul, GrpObj.comp_inv, _root_.mul_assoc]
  unfold lam at h'
  rw [← et, mul_inv_cancel_left] at h'
  have H : KerPow.HasGen L (K := Fin 4) ![(Out.translPt A (y * y'⁻¹)).left, (snd T A).left,
      (fst T A).left ≫ y.left, (fst T A).left ≫ y'.left] ![1, -1, -1, 1] := by
    refine (h1 _ _ (hl _ _ L hL _ _ _).1).1 ?_
    rw [(hl _ _ L hL _ _ _).2, Fin.prod_univ_four]
    have aux : ∀ a b c d e f : Pic (T ⊗ A).left, a * e / (c * f) = b * e / (d * f) →
        a ^ (1 : ℤ) * b ^ (-1 : ℤ) * c ^ (-1 : ℤ) * d ^ (1 : ℤ) = 1 := fun a b c d e f k => by
      have k' := congrArg Additive.ofMul k
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_div, ofMul_zpow, ofMul_one] at k' ⊢
      linear_combination (norm := module) k'
    exact aux _ _ _ _ _ _ h'
  have H' : KerPow.LocGen L (K := Fin 4) (fst T A).left ![(Out.translPt A (y * y'⁻¹)).left, (snd T A).left,
      (fst T A).left ≫ y.left, (fst T A).left ≫ y'.left] ![1, -1, -1, 1] :=
    fun _ => ⟨⊤, trivial, H.pull _ fun _ => rfl⟩
  have B := BoxKernel.locGen_base hL (fst T A).left (K := Fin 2) ![y.left, y'.left] ![-1, 1]
  refine mul_inv_eq_one.1 (KerPow.eq_one_of_locGen hK _ (H'.comb hL B fun U _ g => ?_))
  simp [Fin.prod_univ_four, Fin.prod_univ_two]

end

theorem exists_formIs : Out.Laws → Out.Laws2 → ∀ (K : Type) [Field K] [IsAlgClosed K] (P : Out.PolAV (Sp K)) (M : LB P.A.left), M.IsLB → ∃ s : P.A ⟶ P.A, FormIs P M s := by
  intro hA hB K _ _ P M hM
  obtain ⟨Pic, _, cl, pl, hiso, h1, -, hc, hl, hd⟩ := GlobalTheory.CechPicMul.exists_picardGroup
  have cc := fun {L : LB P.A.left} (hL : L.IsLB) {T : Over (Sp K)} (a b : T ⟶ P.A) => cl_cube @pl @cl hl hL a b
  have ci : ∀ {L : LB P.A.left} (_ : L.IsLB) {T : Over (Sp K)} (a b : T ⟶ P.A), (cubeLB P.A ![a, b] L).IsLB :=
    fun hL _ a b => (hl _ _ _ hL _ _ _).1
  have cp : ∀ {X Y : Scheme.{0}} {L : LB X} (_ : L.IsLB) (f : Y ⟶ X),
      (∃ t : (L.pull f).Gen, t.IsGen) ↔ pl f (cl L) = 1 := fun hL f => by
    rw [← h1 _ _ (hl _ _ _ hL _ _ _).1, (hl _ _ _ hL _ _ _).2, Fintype.prod_unique, zpow_one]
  obtain ⟨hN, eN⟩ := hd _ _ _ (ci P.isLB (fst (P.A ⊗ P.A) P.A ≫ snd _ _) (snd _ _))
    (ci hM (fst (P.A ⊗ P.A) P.A ≫ fst _ _) (snd _ _))
  rw [cc hM, cc P.isLB] at eN
  obtain ⟨Z, i, hi, hZ⟩ := GlobalTheory.SeesawGlobal.exists_closed_triv hA hB K P (P.A ⊗ P.A) _ hN (by
    rw [cp hN, eN, map_div, pl_lam @pl hc, pl_lam @pl hc, lift_snd, lam_one_right, lam_one_right, div_one])

  have hR : ∀ (T : Over (Sp K)) (h : T ⟶ P.A ⊗ P.A),
      lam @pl (cl M) (fst T P.A ≫ h ≫ fst _ _) (snd T P.A) = lam @pl (cl P.L) (fst T P.A ≫ h ≫ snd _ _) (snd T P.A) ↔
        ∃ u : T.left ⟶ Z, u ≫ i = h.left := fun T h => by
    rw [← hZ, cp hN, eN, map_div, pl_lam @pl hc, pl_lam @pl hc, div_eq_one, whiskerRight_snd,
      whiskerRight_fst_assoc, whiskerRight_fst_assoc]
  have uniq := fun {T : Over (Sp K)} (y y' : T ⟶ P.A) => eq_of_lam_eq @pl @cl h1 hc hl P.isLB P.ktriv y y'
  let q : Z ⟶ P.A.left := i ≫ (fst P.A P.A).left
  have w1 : (fst P.A P.A).left ≫ P.A.hom = (P.A ⊗ P.A).hom := Over.w _
  have hmono : Mono q := ⟨fun {W} u v e => by
    let T : Over (Sp K) := Over.mk (u ≫ i ≫ (P.A ⊗ P.A).hom)
    let a : T ⟶ P.A ⊗ P.A := Over.homMk (u ≫ i) (Category.assoc _ _ _)
    let b : T ⟶ P.A ⊗ P.A := Over.homMk (v ≫ i) (by
      have := congrArg (· ≫ P.A.hom) e
      simp only [q, Category.assoc, w1] at this
      exact (Category.assoc _ _ _).trans this.symm)
    have e1 : a ≫ fst _ _ = b ≫ fst _ _ := Over.OverMorphism.ext (by
      simpa only [q, a, b, Over.comp_left, Over.homMk_left, Category.assoc] using e)
    have e2 : a ≫ snd _ _ = b ≫ snd _ _ := uniq _ _ (by
      rw [← (hR T a).2 ⟨u, rfl⟩, ← (hR T b).2 ⟨v, rfl⟩, e1])
    have e3 : a = b := CartesianMonoidalCategory.hom_ext _ _ e1 e2
    exact (cancel_mono i).1 (congrArg (fun z => z.left) e3)⟩
  have := P.isAb.proper
  have : IsProper (fst P.A P.A).left := inferInstanceAs (IsProper (pullback.fst P.A.hom P.A.hom))
  have hq : IsClosedImmersion q := (IsClosedImmersion.iff_isProper_and_mono q).2 ⟨inferInstance, hmono⟩
  obtain ⟨l, hl1, hl2⟩ : ∃ l : ℕ, l.Prime ∧ (l : K) ≠ 0 := by
    by_cases h2 : ((2 : ℕ) : K) = 0
    · refine ⟨3, Nat.prime_three, fun h3 => one_ne_zero (α := K) ?_⟩
      push_cast at h2 h3
      linear_combination h3 - h2
    · exact ⟨2, Nat.prime_two, h2⟩
  have hsurj : Surjective q := ⟨by
    rw [← Set.range_eq_univ, ← q.isClosedEmbedding.isClosed_range.closure_eq]
    refine ((GlobalTheory.PrimePowerTorsion.dense_torsion_and_eq_one hA hB K P l hl1 hl2).1.mono ?_).closure_eq
    refine Set.iUnion₂_subset fun x ⟨j, hj⟩ => ?_
    obtain ⟨y, -, hy⟩ := GlobalTheory.T.exists_torsion_cubeLB_iso_polarisation_translate hA hB K P M (l ^ j) x hM (by push_cast; exact pow_ne_zero _ hl2) hj
    rw [← hiso _ _ _ (ci hM _ _) (ci P.isLB _ _), cc hM, cc P.isLB] at hy
    have hy' := congrArg (pl (snd (𝟙_ (Over (Sp K))) P.A).left) hy
    rw [pl_lam @pl hc, pl_lam @pl hc, Category.comp_id, ← Category.assoc, ← Category.assoc,
      toUnit_unique (_ ≫ _) (fst _ _)] at hy'
    obtain ⟨u, hu⟩ := (hR _ (lift x y)).1 (by rw [lift_fst, lift_snd]; exact hy')
    have e : u ≫ q = x.left := by
      rw [← Category.assoc, hu, ← Over.comp_left, lift_fst]
    rintro _ ⟨z, rfl⟩
    exact ⟨u z, by rw [← e]; rfl⟩⟩
  have := polAV_isIntegral_of_isAlgClosed K P
  have : IsIso q := isIso_of_isClosedImmersion_of_surjective q
  let h : P.A ⟶ P.A ⊗ P.A := Over.homMk (inv q ≫ i) (by
    rw [← w1, Category.assoc, ← Category.assoc i, IsIso.inv_hom_id_assoc])
  have h₁ : h ≫ fst _ _ = 𝟙 _ := Over.OverMorphism.ext (by
    change (inv q ≫ i) ≫ _ = 𝟙 _
    rw [Category.assoc, IsIso.inv_hom_id])
  have key := (hR _ h).2 ⟨inv q, rfl⟩
  rw [h₁, Category.comp_id] at key
  refine ⟨h ≫ snd _ _, hA.rigidity _ _ _ P.isAb P.isAb _ ?_, ?_⟩
  · have e1 : (1 : 𝟙_ (Over (Sp K)) ⟶ P.A) = η[P.A] := by rw [Hom.one_def]; simp
    rw [← e1]
    refine uniq _ _ ?_
    have k := congrArg (pl ((1 : 𝟙_ (Over (Sp K)) ⟶ P.A) ▷ P.A).left) key
    rw [pl_lam @pl hc, pl_lam @pl hc, whiskerRight_snd, whiskerRight_fst_assoc, whiskerRight_fst,
      MonObj.comp_one, lam_one_left] at k
    rw [← k, MonObj.comp_one, lam_one_left]
  · change LBIso (cubeLB P.A ![fst _ _, snd _ _] M) _
    rw [← hiso _ _ _ (ci hM _ _) (ci P.isLB _ _), cc hM, cc P.isLB]
    have k := congrArg (pl (lift (snd P.A P.A) (fst P.A P.A)).left) key
    rw [pl_lam @pl hc, pl_lam @pl hc, lift_fst_assoc, lift_fst, lift_snd] at k
    rw [lam_comm, k, lam_comm]

end GlobalTheory.BundleForm
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.ZM

theorem isQProjOver_opens_of_noetherian {o : Type} [CommRing o] [IsNoetherianRing o] {X : Scheme.{0}} {s : X ⟶ Sp o}
    (h : IsQProjOver s) (U : X.Opens) : IsQProjOver (U.ι ≫ s) := by
  obtain ⟨N, i, hi, hq, rfl⟩ := h
  have : IsProper (PSpace.str o N) := isProper_str o N
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (i ≫ PSpace.str o N)
  exact ⟨N, U.ι ≫ i, inferInstance, inferInstance, by simp⟩

theorem isIso_of_closedPoint_mem_range {R : Type} [CommRing R] [IsLocalRing R] {Z : Scheme.{0}} (z : Z ⟶ Sp R)
    [IsOpenImmersion z] (h : (IsLocalRing.closedPoint R : Sp R) ∈ Set.range z) : IsIso z := by
  have hs : Function.Surjective z := by
    intro p
    exact (IsLocalRing.specializes_closedPoint (R := R) p).mem_open z.isOpenEmbedding.isOpen_range h
  have : Epi z.base := (TopCat.epi_iff_surjective _).2 hs
  exact IsOpenImmersion.isIso z

theorem TObj.exists_hasTh_of_isLocalRing (h1 : Out.Laws) (h2 : Out.Laws2) {o : Type} [CommRing o] {g N' : ℕ} {J : Type}
    {b : TBase o (N' ^ 2)} (hN : Odd N') {R : Type} [CommRing R] [IsLocalRing R] {s' : Sp R ⟶ Sp o}
    (t : TObj g (N' ^ 2) J b s') : ∃ v, t.HasTh (𝟙 (Sp R)) v := by
  obtain ⟨R', _, z, v, hz, hp, hv⟩ := GlobalTheory.T.exists_thetaConstants_locally_on_base h1 h2 o g N' J b _ s' t hN (IsLocalRing.closedPoint R)
  have := isIso_of_closedPoint_mem_range z hp
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (inv z)
  have := GlobalTheory.T.hasThetaConstants_ring_baseChange h2 o g N' J b _ s' t R' R φ.hom z v hv
  have e : spMap φ.hom ≫ z = 𝟙 (Sp R) := by
    change Spec.map φ ≫ z = _
    rw [hφ, IsIso.inv_hom_id]
  rw [e] at this
  exact ⟨_, this⟩

theorem WFam.qproj_flat_reduced_ext : Out.Laws → Out.Laws2 → ∀ (o : Type) [CommRing o] (g n N' : ℕ) (J : Type) (b : TBase o (N' ^ 2)) (em : o →+* ℂ) (C : TObj g (N' ^ 2) J b (spMap em) → Prop) Mat κ (F : WFam n em C Mat κ), Odd N' → (IsQProjOver (F.U.ι ≫ F.Y.s) ∨ ¬ IsNoetherianRing o) ∧ Flat (F.U.ι ≫ F.Y.s) ∧ IsReduced F.U.toScheme ∧ ∀ (R : Type) [CommRing R] [IsLocalRing R] (x y : Sp R ⟶ F.U.toScheme) (s' : Sp R ⟶ Sp o) (t : TObj g (N' ^ 2) J b s'), x ≫ F.U.ι ≫ F.Y.s = y ≫ F.U.ι ≫ F.Y.s → TMap t F.univ x → TMap t F.univ y → x = y := by
  intro h1 h2 o _ g n N' J b em C Mat κ F hN
  have := F.Y.flat
  have := F.Y.reduced
  refine ⟨?_, inferInstance, isReduced_of_isOpenImmersion F.U.ι, ?_⟩
  · by_cases hn : IsNoetherianRing o
    · exact Or.inl (isQProjOver_opens_of_noetherian F.Y.qproj F.U)
    · exact Or.inr hn
  · intro R _ _ x y s' t hxy hx hy
    obtain ⟨v, hv⟩ := TObj.exists_hasTh_of_isLocalRing h1 h2 hN t
    have vx := (GlobalTheory.T.hasThetaConstants_iff_of_thetaLevelPullback o g N' J b _ _ F.univ _ s' t x R (𝟙 _) v hx).1 hv
    have vy := (GlobalTheory.T.hasThetaConstants_iff_of_thetaLevelPullback o g N' J b _ _ F.univ _ s' t y R (𝟙 _) v hy).1 hv
    rw [Category.id_comp] at vx vy
    have cx := (F.th R x v).1 vx
    have cy := (F.th R y v).1 vy
    obtain ⟨β, hβ⟩ := Spec.map_surjective (x ≫ F.U.ι ≫ F.Y.s)
    have bx : (x ≫ F.U.ι) ≫ F.Y.s = spMap β.hom := by rw [Category.assoc, ← hβ]; rfl
    have by' : (y ≫ F.U.ι) ≫ F.Y.s = spMap β.hom := by rw [Category.assoc, ← hxy, ← hβ]; rfl
    have hin := F.Y.loc R β.hom _ v bx cx
    have := (F.Y.pts R β.hom v hin).unique ⟨bx, cx⟩ ⟨by', cy⟩
    exact (cancel_mono F.U.ι).1 this

end GlobalTheory.ZM
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ZM

theorem _root_.GlobalTheory.T.relAmple_extended_principalPolarisation_dvr : Laws → Laws2 → ∀ (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K] (P : PolAV (Sp K)) (B : Over (Sp V)) [GrpObj B] [IsCommMonObj B] (M : GlobalTheory.UU.CP B) (φ : P.A.left ⟶ B.left), IsAbelianScheme B → IsGrpPullback P.A B (spMap (algebraMap V K)) φ → LBIso P.L (M.L.L.pull φ) → IsAdicComplete (IsLocalRing.maximalIdeal V) V → RelAmple B M.L.L := by
  first | exact @GlobalTheory.ExtAmple.relAmple_extension | exact GlobalTheory.ExtAmple.relAmple_extension | (intros; apply GlobalTheory.ExtAmple.relAmple_extension <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.LevelSpread

theorem exists_closed_eq {S : Scheme.{0}} {Z A : Over S} [IsSeparated A.hom] (u u' : Z ⟶ A) :
    ∃ C : Set Z.left, IsClosed C ∧ ∀ (K : Type) [Field K] (x : Sp K ⟶ S) (h : Over.mk x ⟶ Z),
      h ≫ u = h ≫ u' ↔ Set.range h.left ⊆ C := by
  have : IsClosedImmersion (equalizer.ι u u').left := inferInstance
  refine ⟨Set.range (equalizer.ι u u').left, (Scheme.Hom.isClosedEmbedding _).isClosed_range,
    fun K _ x h => ⟨fun e => ?_, fun e => ?_⟩⟩
  · rintro _ ⟨p, rfl⟩
    refine ⟨(equalizer.lift h e).left p, ?_⟩
    rw [← Scheme.Hom.comp_apply, ← Over.comp_left, equalizer.lift_ι]
  · have : IsReduced (Over.mk x).left := inferInstanceAs (IsReduced (Sp K))
    obtain ⟨f, hf⟩ := exists_lift_closedImmersion_of_dense (equalizer.ι u u').left h.left Set.univ dense_univ
      fun p _ => e ⟨p, rfl⟩
    apply Over.OverMorphism.ext
    rw [Over.comp_left, Over.comp_left, ← hf, Category.assoc, Category.assoc, ← Over.comp_left, ← Over.comp_left,
      equalizer.condition]

theorem appTop_eq_zero_iff {Z : Scheme.{0}} (f : Γ(Z, ⊤)) {K : Type} [Field K] (h : Sp K ⟶ Z) :
    h.appTop.hom f = 0 ↔ Set.range h ⊆ (Z.basicOpen f : Set Z)ᶜ := by
  rw [← basicOpen_eq_bot_iff, ← Scheme.preimage_basicOpen_top, eq_bot_iff]
  constructor
  · rintro e _ ⟨p, rfl⟩ hp
    exact e hp
  · intro e p hp
    exact e ⟨p, rfl⟩ hp

theorem map_fnOn_apply {L k : Type} [CommRing L] [CommRing k] {T : Scheme.{0}} (g : T ⟶ Sp L) (h : Sp k ⟶ T)
    (β : L →+* k) (e : h ≫ g = spMap β) (c : L) :
    h.appTop.hom (LevCover.fnOn g c) = (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom (β c) := by
  have h1 : (h ≫ g).appTop = g.appTop ≫ h.appTop := Scheme.Hom.comp_appTop _ _
  have h2 := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom β)
  have h3 := congrArg (fun φ => φ.hom c) h2
  rw [e] at h1
  have h4 := congrArg (fun φ => φ.hom ((Scheme.ΓSpecIso (CommRingCat.of L)).inv.hom c)) h1
  exact h4.symm.trans h3.symm

theorem exists_unitOn {K : Type} [CommRing K] (c : Γ(Sp K, ⊤)ˣ) : ∃ ζ : Kˣ, c = unitOn ζ := by
  refine ⟨Units.map (Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom.toMonoidHom c, Units.ext ?_⟩
  exact ((Scheme.ΓSpecIso (CommRingCat.of K)).hom_inv_id_apply c).symm

theorem pow_eq_iff {L K : Type} [CommRing L] [Field K] {T : Scheme.{0}} (g : T ⟶ Sp L) (h : Sp K ⟶ T)
    (β : L →+* K) (e : h ≫ g = spMap β) (z : L) (c : Γ(T, ⊤)ˣ) (ζ : Kˣ) (m : ℕ)
    (hc : Units.map h.appTop.hom.toMonoidHom c = unitOn ζ) :
    (ζ : K) ^ m = β z ↔ Set.range h ⊆ (T.basicOpen ((c : Γ(T, ⊤)) ^ m - LevCover.fnOn g z) : Set T)ᶜ := by
  have h1 : h.appTop.hom c = (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom ζ := congrArg Units.val hc
  rw [← appTop_eq_zero_iff, map_sub, map_pow, h1, map_fnOn_apply g h β e, ← map_pow, sub_eq_zero]
  exact ((Scheme.ΓSpecIso (CommRingCat.of K)).symm.commRingCatIsoToRingEquiv.injective.eq_iff).symm

end GlobalTheory.LevelSpread

namespace GlobalTheory

open LevelSpread

theorem exists_levelIsometry_of_dense : Out.Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (S : Scheme.{0}) (P : Out.PolAV S) (act : 𝓞 E → (P.A ⟶ P.A)) (o : Type) [CommRing o] (s : S ⟶ Sp o) (z : o) (κ : Type) (lam : κ → D.La) (pt : κ → (Out.baseOver S ⟶ P.A)) (n m : ℕ), 0 < n → Dense {p : S | ∃ (K : Type) (_ : Field K) (x : Sp K ⟶ S) (β : o →+* K) (ζ : Kˣ) (ev : D.La → (Over.mk x ⟶ P.A)), (n : K) ≠ 0 ∧ p ∈ Set.range x ∧ x ≫ s = spMap β ∧ IsPrimitiveRoot ζ n ∧ (∀ a c, ev (a + c) = ev a * ev c) ∧ (∀ a, ev a ^ n = 1) ∧ (∀ (c : 𝓞 E) a, ev (c • a) = ev a ≫ act c) ∧ (∀ a c, Out.WeilIs P.A P.L n (ev a) (ev c) (unitOn (ζ ^ D.EF a c))) ∧ (ζ : K) ^ m = β z ∧ ∀ i, ev (lam i) ^ m = (Over.homMk x (by simp) : Over.mk x ⟶ Out.baseOver S) ≫ pt i} → ∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ S) (β : o →+* K), (n : K) ≠ 0 → x ≫ s = spMap β → ∃ (ζ : Kˣ) (ev : D.La → (Over.mk x ⟶ P.A)), IsPrimitiveRoot ζ n ∧ (∀ a c, ev (a + c) = ev a * ev c) ∧ (∀ a, ev a ^ n = 1) ∧ (∀ (c : 𝓞 E) a, ev (c • a) = ev a ≫ act c) ∧ (∀ a c, Out.WeilIs P.A P.L n (ev a) (ev c) (unitOn (ζ ^ D.EF a c))) ∧ (ζ : K) ^ m = β z ∧ ∀ i, ev (lam i) ^ m = (Over.homMk x (by simp) : Over.mk x ⟶ Out.baseOver S) ≫ pt i := by
  intro hL E _ _ _ H D S P act o _ s z κ lam pt n m hn hD K _ _ x β hK hx
  obtain ⟨hfree, hfin⟩ := LevCover.datum_free D
  have := P.isAb.comm
  have := P.isAb.proper
  obtain ⟨Z, et, c, hu, hadd, hpow, hc, hprim, hrep, hlast⟩ := GlobalTheory.T.exists_finite_scheme_latticeTorsionHom_primitiveRoot S P.A n D.La P.isAb hn
  choose C1 hC1 HC1 using fun (b : 𝓞 E) (a : D.La) => exists_closed_eq (et (b • a)) (et a ≫ act b)
  choose C2 hC2 HC2 using fun (a a' : D.La) => GlobalTheory.exists_clopen_weilIs_iff hL S P n Z (et a) (et a')
    (c ^ D.EF a a') hn hu (hpow _) (hpow _)
    (by rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hc, one_zpow])
  let q : Z ⟶ Out.baseOver S := Over.homMk Z.hom (by simp)
  choose C4 hC4 HC4 using fun i : κ => exists_closed_eq (et (lam i) ^ m) (q ≫ pt i)
  let C3 : Set Z.left := (Z.left.basicOpen ((c : Γ(Z.left, ⊤)) ^ m - LevCover.fnOn (Z.hom ≫ s) z) : Set Z.left)ᶜ
  let C : Set Z.left := (⋂ b, ⋂ a, C1 b a) ∩ (⋂ a, ⋂ a', (C2 a a' : Set Z.left)) ∩ C3 ∩ ⋂ i, C4 i
  have hC : IsClosed C :=
    (((isClosed_iInter fun b => isClosed_iInter fun a => hC1 b a).inter
      (isClosed_iInter fun a => isClosed_iInter fun a' => hC2 a a')).inter
      (Z.left.basicOpen _).isOpen.isClosed_compl).inter (isClosed_iInter hC4)
  have key : ∀ (K : Type) [Field K] (x : Sp K ⟶ S) (β : o →+* K) (ζ : Kˣ) (h : Over.mk x ⟶ Z), x ≫ s = spMap β →
      Units.map h.left.appTop.hom.toMonoidHom c = unitOn ζ →
      (((∀ (b : 𝓞 E) a, h ≫ et (b • a) = (h ≫ et a) ≫ act b) ∧
        (∀ a a', Out.WeilIs P.A P.L n (h ≫ et a) (h ≫ et a') (unitOn (ζ ^ D.EF a a'))) ∧ (ζ : K) ^ m = β z ∧
        ∀ i, (h ≫ et (lam i)) ^ m = (Over.homMk x (by simp) : Over.mk x ⟶ Out.baseOver S) ≫ pt i) ↔
        Set.range h.left ⊆ C) := by
    intro K _ x β ζ h hx hζ
    have hw : h.left ≫ Z.hom = x := Over.w h
    have hq : h ≫ q = (Over.homMk x (by simp) : Over.mk x ⟶ Out.baseOver S) := Over.OverMorphism.ext hw
    have h3 := pow_eq_iff (Z.hom ≫ s) h.left β (by rw [← Category.assoc, hw, hx]) z c ζ m hζ
    have hz : ∀ k : ℤ, unitOn (ζ ^ k) = Units.map h.left.appTop.hom.toMonoidHom (c ^ k) := fun k => by
      rw [map_zpow, hζ, unitOn, unitOn, map_zpow]
    simp only [C, Set.subset_inter_iff, Set.subset_iInter_iff, and_assoc]
    refine and_congr (forall₂_congr fun b a => ?_) (and_congr (forall₂_congr fun a a' => ?_)
      (and_congr h3 (forall_congr' fun i => ?_)))
    · rw [← HC1 b a K x h, Category.assoc]
    · rw [← HC2 a a' _ h, hz]
    · rw [← HC4 i K x h, ← hq, Category.assoc, MonObj.comp_pow]
  have hdense : Dense (Z.hom '' C) := by
    refine hD.mono ?_
    rintro _ ⟨K, _, x, β, ζ, ev, hK, ⟨p, rfl⟩, hx, h1, h2, h3, h4⟩
    obtain ⟨h, hh, hζ⟩ := hrep K x ev ζ hK h2 h3 h1
    obtain rfl : (fun a => h ≫ et a) = ev := funext hh
    have hw : h.left ≫ Z.hom = x := Over.w h
    exact ⟨h.left p, (key K x β ζ h hx hζ).1 h4 ⟨p, rfl⟩, by rw [← Scheme.Hom.comp_apply, hw]⟩
  obtain ⟨h, hh⟩ := hlast C hC K x hK (by rw [hdense.closure_eq]; exact Set.subset_univ _)
  obtain ⟨ζ, hζ⟩ := exists_unitOn (K := K) (Units.map h.left.appTop.hom.toMonoidHom c)
  exact ⟨ζ, fun a => h ≫ et a, hprim K h.left ζ hζ, fun a a' => by beta_reduce; rw [hadd, MonObj.comp_mul],
    fun a => by beta_reduce; rw [← MonObj.comp_pow, hpow, MonObj.comp_one], (key K x β ζ h hx hζ).2 hh⟩

end GlobalTheory
end

section

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory


open AdjointOfPairing in
theorem lbIso_cubeLB_of_pairing_adjoint : Out.Laws → ∀ (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (P : Out.PolAV (Sp k)) (a a' : P.A ⟶ P.A), IsMonHom a → IsMonHom a' → (∀ (n : ℕ) (x y : 𝟙_ (Over (Sp k)) ⟶ P.A) (c : Γ((𝟙_ (Over (Sp k))).left, ⊤)ˣ), 0 < n → x ^ n = 1 → y ^ n = 1 → Out.WeilIs P.A P.L n (x ≫ a) y c → Out.WeilIs P.A P.L n x (y ≫ a') c) → LBIso (cubeLB P.A ![fst P.A P.A ≫ a, snd P.A P.A] P.L) (cubeLB P.A ![fst P.A P.A, snd P.A P.A ≫ a'] P.L) := by
  intro hl k _ _ _ P a a' ha ha' H
  have := P.isAb.comm
  have out : ∀ r : P.A ⟶ P.A ⊗ P.A, (∃ t : LB.Gen (LB.LinComb P.L (fun i => r.left ≫ Out.rosatiφ P.A a a' i)
      Out.rosatiε), t.IsGen) → ∃ t : ((LB.LinComb P.L (Out.rosatiφ P.A a a') Out.rosatiε).pull r.left).Gen,
        t.IsGen := fun r ⟨t, ht⟩ => gen_chartPull (chartPullOut P.L _ _ _ _ fun _ => rfl) t ht
  obtain ⟨t, ht⟩ := GlobalTheory.T.seesaw_triviality_on_dense_fibres_product_abelian hl.globalFns k P.A P.A (LB.LinComb P.L (Out.rosatiφ P.A a a') Out.rosatiε) P.L
    P.isAb P.isAb P.isLB P.ample
    (DVR.linComb_isLB P.L P.isLB _ _)
    (out _ (exists_gen_of_formEq_zero P.isLB fun U _ h => by
      rw [prod_ros, MonObj.one_comp, _root_.one_mul, _root_.one_mul]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_one]
      abel))
    ((TorsionDense.dense_torsion P hl.irred hl.kerPow).mono (by
      intro z hz
      simp only [Set.mem_iUnion] at hz ⊢
      obtain ⟨x, ⟨n, hn, hxn⟩, q, rfl⟩ := hz
      exact ⟨x, out _ (exists_gen_fibre hl P a a' n (Nat.cast_ne_zero.2 hn.ne') x hxn
        fun y c hy => H n x y c hn hxn hy), q, rfl⟩))
    (out _ (exists_gen_of_formEq_zero P.isLB fun U _ h => by
      rw [prod_ros, MonObj.one_comp, _root_.mul_one, _root_.mul_one]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_one]
      abel))
  obtain ⟨u, hu, -⟩ := exists_gen P.isLB
    (φ' := Sum.elim (fun I : ULift.{0} (Finset (Fin 2)) => (psum P.A ![fst P.A P.A, snd P.A P.A ≫ a'] I.down).left)
      (fun I : ULift.{0} (Finset (Fin 2)) => (psum P.A ![fst P.A P.A ≫ a, snd P.A P.A] I.down).left))
    (ε' := Sum.elim (fun I => (-1) ^ (2 - I.down.card)) (fun I => -(-1) ^ (2 - I.down.card)))
    (fun V _ h => by
      have p := prod_ros a a' (fst P.A P.A) (snd P.A P.A) h
      rw [lift_fst_snd] at p
      simp only [Over.id_left, Category.id_comp] at p
      refine (DVR.prod_neg _ _ p).trans (Eq.trans ?_ (DVR.prod_sum₂ (K := ULift.{0} (Finset (Fin 2)))
        (K' := ULift.{0} (Finset (Fin 2))) (U := V) _ (NormRos.prod_square (fst P.A P.A) (snd P.A P.A ≫ a') h)
        (DVR.prod_neg _ _ (NormRos.prod_square (fst P.A P.A ≫ a) (snd P.A P.A) h))).symm)
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel)
    (LB.invGen P.L _ _ t) (DVR.invGen_isGen _ _ _ _ ht)
  exact lbIso_of_gen u hu

end GlobalTheory
end
end
