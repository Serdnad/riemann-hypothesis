module

public import Formalism.LocalRingCardinality.AdicCompletionLocal.InstIsAdicCompleteOCSpanSingletonSetCast
public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Development.AbelianVarietyTheory.CrystallinePeriods.Bundle001
public import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
public import Formalism.SharpRestriction.GrowthBounds.UnramifiedQuadraticSetting
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle054
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingStalkGeneric
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLineBundleGeneratorExtendingDensePart
public import Mathlib.Basic.Complex.Basic
public import Mathlib.RepresentationTheory.Irreducible
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle079
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle080
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
public import Mathlib.NumberTheory.Cyclotomic.CyclotomicCharacter
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Coalgebra.CoassocSimps
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle010
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsNotCongPow
public import Formalism.ConjugateSelfDual.Bundle001
import ReciprocityTheory.GaloisValuations.GlobalA
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasExponentZeroIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes

@[expose] public section

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.MemLoc

theorem coeff_galois_tilt (l : ℕ) [Fact l.Prime] (g : GQ l) (x : OCb l) (n : ℕ) (y : OC l)
    (h : PreTilt.coeff n x = Ideal.Quotient.mk (Ideal.span {((l : ℕ) : OC l)}) y) :
    ∃ y' : OC l, (y' : PadicComplex l) = Per.σC g (y : PadicComplex l) ∧
      PreTilt.coeff n (Per.σF g x) = Ideal.Quotient.mk (Ideal.span {((l : ℕ) : OC l)}) y' :=
  ⟨Per.σO g y, GlobalTheory.RingIface.sigO_coe (l := l) g y,
    GlobalTheory.AdicMaps.coeff_galois l g x n y h⟩

end GlobalTheory.MemLoc
end

section

noncomputable section

namespace GlobalTheory.GlobApx

open Formalism.MainNotions.G

theorem mulVec_mem_colSpan {R K : Type} [CommRing R] [Field K] [Algebra R K] {k : ℕ}
    (g : Matrix (Fin k) (Fin k) K) (w : Fin k → R) :
    g.mulVec (fun j => algebraMap R K (w j)) ∈ colSpan R g := by
  have : g.mulVec (fun j => algebraMap R K (w j)) = ∑ j, w j • fun i => g i j := by
    funext i
    simp [Matrix.mulVec, dotProduct, Algebra.smul_def, mul_comm]
  rw [this]
  exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

theorem exists_pow_smul_ge {R K : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K]
    [Algebra R K] [IsFractionRing R K] {π : R} (hπ : Irreducible π) {k : ℕ} (g : Matrix (Fin k) (Fin k) K) :
    ∃ a : ℕ, ∀ N, a ≤ N → ∃ g0 : Matrix (Fin k) (Fin k) R,
      algebraMap R K π ^ N • g = g0.map (algebraMap R K) := by
  obtain ⟨a, g0, h⟩ := GlobalTheory.GO.TupApx.exists_pow_smul (K := K) hπ g
  refine ⟨a, fun N hN => ?_⟩
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hN
  refine ⟨π ^ d • g0, ?_⟩
  rw [pow_add, mul_comm, mul_smul, h]
  ext i j
  simp only [Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, map_mul, map_pow]

theorem exists_glob_approx : ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (W Q : ι → Type) [∀ q, CommRing (W q)] [∀ q, IsDomain (W q)] [∀ q, IsDiscreteValuationRing (W q)] [∀ q, Field (Q q)] [∀ q, Algebra (W q) (Q q)] [∀ q, IsFractionRing (W q) (Q q)] {F : Type} [Field F] (f : ∀ q, F →+* Q q) (π : ∀ q, W q), (∀ q, Irreducible (π q)) → ∀ (t : F), (∀ q, f q t = algebraMap (W q) (Q q) (π q)) → (∀ (y : ∀ q, W q) (N : ℕ), ∃ x : F, ∀ q, ∃ z : W q, f q x = algebraMap (W q) (Q q) (y q + π q ^ N * z)) → ∀ {n : ℕ} (g : ∀ q, Matrix (Fin n) (Fin n) (Q q)), (∀ q, IsUnit (g q).det) → ∀ (q0 : ι), ∃ (B : Matrix (Fin n) (Fin n) F) (u : Matrix (Fin n) (Fin n) (W q0)), IsUnit u.det ∧ B.map (f q0) = g q0 * u.map (algebraMap (W q0) (Q q0)) ∧ ∀ q, q ≠ q0 → ∀ c, (fun i => f q (B i c)) ∈ Formalism.MainNotions.G.colSpan (W q) (g q) := by
  intro ι _ _ W Q _ _ _ _ _ _ F _ f π hπ t ht hd n g hg q0
  have hp0 : ∀ q, algebraMap (W q) (Q q) (π q) ≠ 0 := fun q =>
    (map_ne_zero_iff _ (IsFractionRing.injective (W q) (Q q))).2 (hπ q).ne_zero
  choose a ha using fun q => exists_pow_smul_ge (hπ q) (g q)
  choose b hb using fun q => exists_pow_smul_ge (hπ q) (g q)⁻¹
  set M := Finset.univ.sup (fun q => a q + b q) with hMdef
  have hM : ∀ q, a q ≤ M ∧ b q ≤ M := fun q => by
    have := Finset.le_sup (f := fun q => a q + b q) (Finset.mem_univ q)
    constructor <;> omega
  choose G hG using fun q => ha q M (hM q).1
  choose H hH using fun q => hb q M (hM q).2
  choose x hx using fun i j => hd (Pi.single (M := W) q0 (G q0 i j)) (2 * M + 1)
  choose z hz using hx
  have hB : ∀ q i j, f q ((t ^ M)⁻¹ * x i j) = (algebraMap (W q) (Q q) (π q) ^ M)⁻¹ *
      (algebraMap (W q) (Q q) (Pi.single (M := W) q0 (G q0 i j) q) +
        algebraMap (W q) (Q q) (π q) ^ (2 * M + 1) * algebraMap (W q) (Q q) (z i j q)) := by
    intro q i j
    rw [map_mul, map_inv₀, map_pow, ht, hz, map_add (f := _), map_mul, map_pow]
  refine ⟨Matrix.of fun i j => (t ^ M)⁻¹ * x i j, 1 + π q0 • (H q0 * Matrix.of fun i j => z i j q0), ?_, ?_, ?_⟩
  · rw [← IsLocalRing.residue_ne_zero_iff_isUnit, RingHom.map_det]
    have hr : IsLocalRing.residue (W q0) (π q0) = 0 := by
      rw [IsLocalRing.residue_eq_zero_iff]; exact (hπ q0).not_isUnit
    have : (IsLocalRing.residue (W q0)).mapMatrix (1 + π q0 • (H q0 * Matrix.of fun i j => z i j q0)) = 1 := by
      rw [map_add (f := _), map_one]
      have : (IsLocalRing.residue (W q0)).mapMatrix (π q0 • (H q0 * Matrix.of fun i j => z i j q0)) = 0 := by
        ext i j; simp [hr]
      rw [this, add_zero]
    rw [this]; simp
  · have e1 : (1 + π q0 • (H q0 * Matrix.of fun i j => z i j q0)).map (algebraMap (W q0) (Q q0)) =
        1 + algebraMap (W q0) (Q q0) (π q0) • ((H q0).map (algebraMap (W q0) (Q q0)) *
          (Matrix.of fun i j => z i j q0).map (algebraMap (W q0) (Q q0))) := by
      rw [← Matrix.map_mul]
      ext i j
      simp only [Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, map_add (f := _), map_mul,
        Matrix.one_apply, apply_ite (algebraMap (W q0) (Q q0)), map_one, map_zero]
    rw [e1, ← hH q0, mul_add, mul_one, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_smul, ← Matrix.mul_assoc,
      Matrix.mul_nonsing_inv _ (hg q0), Matrix.one_mul]
    ext i j
    have h2 := congrFun (congrFun (hG q0) i) j
    simp only [Matrix.smul_apply, Matrix.map_apply, smul_eq_mul] at h2
    simp only [Matrix.map_apply, Matrix.of_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    rw [hB, Pi.single_eq_same, ← h2]
    have := hp0 q0
    field_simp
    ring
  · intro q hq c
    set zc : Fin n → W q := fun i => z i c q
    have hv : (fun i => f q ((Matrix.of fun i j => (t ^ M)⁻¹ * x i j) i c)) =
        (g q).mulVec (fun j => algebraMap (W q) (Q q) ((π q • (H q).mulVec zc) j)) := by
      have e2 : (fun j => algebraMap (W q) (Q q) ((π q • (H q).mulVec zc) j)) =
          algebraMap (W q) (Q q) (π q) • ((H q).map (algebraMap (W q) (Q q))).mulVec
            (fun j => algebraMap (W q) (Q q) (zc j)) := by
        funext j

        simp [Matrix.mulVec, dotProduct, map_sum, map_mul]
      rw [e2, ← hH q, Matrix.mulVec_smul, Matrix.smul_mulVec, Matrix.mulVec_smul, Matrix.mulVec_mulVec,
        Matrix.mul_nonsing_inv _ (hg q), Matrix.one_mulVec]
      funext i
      simp only [Matrix.of_apply, Pi.smul_apply, smul_eq_mul]
      rw [hB, Pi.single_eq_of_ne hq, map_zero, zero_add]
      have := hp0 q
      field_simp
      ring
    rw [hv]
    exact mulVec_mem_colSpan _ _

end GlobalTheory.GlobApx
end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per
namespace GlobalTheory.MemLoc

theorem _root_.GlobalTheory.MemLoc.exists_cyclotomicChar : ∀ (l : ℕ) [Fact l.Prime], ∃ χ : _root_.Formalism.BasicNotions.Loc.GQ l →* ℤ_[l]ˣ,
    ∀ (g : _root_.Formalism.BasicNotions.Loc.GQ l) (m : ℕ) (x : _root_.Formalism.BasicNotions.Loc.Om l), x ^ (l ^ m) = 1 →
      g x = x ^ (PadicInt.toZModPow m (χ g : ℤ_[l])).val := by
  intro l _
  haveI : ∀ i, HasEnoughRootsOfUnity (_root_.Formalism.BasicNotions.Loc.Om l) (l ^ i) := fun i => by
    unfold _root_.Formalism.BasicNotions.Loc.Om
    infer_instance
  let ρ : _root_.Formalism.BasicNotions.Loc.GQ l →* (_root_.Formalism.BasicNotions.Loc.Om l ≃+* _root_.Formalism.BasicNotions.Loc.Om l) :=
    { toFun := fun g => (g : _root_.Formalism.BasicNotions.Loc.Om l ≃+* _root_.Formalism.BasicNotions.Loc.Om l), map_one' := rfl, map_mul' := fun _ _ => rfl }
  exact ⟨(cyclotomicCharacter (_root_.Formalism.BasicNotions.Loc.Om l) l).comp ρ,
    fun g m x hx => cyclotomicCharacter.spec l (g : _root_.Formalism.BasicNotions.Loc.Om l ≃+* _root_.Formalism.BasicNotions.Loc.Om l) x hx⟩

end GlobalTheory.MemLoc
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

set_option backward.isDefEq.respectTransparency false

namespace GlobalTheory.GenExtendDense

open GlobalTheory.GenericExtend GlobalTheory.DvrModel

theorem gm_eq_of_corr {X Y U HU H Z : Scheme.{0}} {L : LB X} (hL : L.IsLB) {I : Type} [Fintype I]
    {φ : I → (H ⟶ X)} {ε : I → ℤ} {jH : HU ⟶ H} {e : Y ⟶ H} {j : U ⟶ Y} {eU : U ⟶ HU}
    (heU : eU ≫ jH = j ≫ e)
    {t : LB.Gen (LB.LinComb L (fun i => jH ≫ φ i) ε)}
    {ρ : LB.Gen (LB.LinComb L (fun i => e ≫ φ i) ε)} (ht : t.IsGen) (hρ : ρ.IsGen)
    (hc : LB.Gen.Corr L _ _ _ _ (LB.pullGen L _ _ t eU) (LB.pullGen L _ _ ρ j))
    (κ : Z ⟶ U) (z : Z) (a : I → L.ι) (ha : e (j (κ z)) ∈ LB.wchart L φ a) :
    gm (κ ≫ eU) z (LB.wchart L (fun i => jH ≫ φ i) a) (t.s a) =
      gm (κ ≫ j) z (LB.wchart L (fun i => e ≫ φ i) a) (ρ.s a) := by
  choose Jg hJg using fun ψ : Z ⟶ X => exists_chart hL (ψ z)
  have hG : Good L z Jg := hJg
  have hv := val_corr hG hc κ
  rw [val_pull hG, val_pull hG] at hv
  have hw : ∀ k, (κ ≫ eU) ≫ jH ≫ φ k = (κ ≫ j) ≫ e ≫ φ k := fun k => by
    simp only [Category.assoc, reassoc_of% heU]
  let a' : I → L.ι := fun k => Jg ((κ ≫ eU) ≫ jH ≫ φ k)
  have ha' : a' = fun k => Jg ((κ ≫ j) ≫ e ≫ φ k) := funext fun k => congrArg Jg (hw k)
  rw [val_of t (κ ≫ eU) z Jg a' (fun k => rfl),
    val_of ρ (κ ≫ j) z Jg a' (fun k => by rw [ha'])] at hv
  have hpt : jH ((κ ≫ eU) z) = e ((κ ≫ j) z) := by
    rw [← Scheme.Hom.comp_apply, Category.assoc, heU, ← Category.assoc, Scheme.Hom.comp_apply]
  have h1 : (κ ≫ eU) z ∈ LB.wchart L (fun i => jH ≫ φ i) a :=
    (wchart_comp L jH φ a).ge (show jH ((κ ≫ eU) z) ∈ LB.wchart L φ a by rw [hpt]; exact ha)
  have h2 : (κ ≫ j) z ∈ LB.wchart L (fun i => e ≫ φ i) a := (wchart_comp L e φ a).ge ha
  have h1' : (κ ≫ eU) z ∈ LB.wchart L (fun i => jH ≫ φ i) a' := hG.mem (fun i => jH ≫ φ i) (κ ≫ eU)
  have h2' : (κ ≫ j) z ∈ LB.wchart L (fun i => e ≫ φ i) a' := by
    rw [ha']; exact hG.mem (fun i => e ≫ φ i) (κ ≫ j)
  have htr : trF (L := L) (fun i => jH ≫ φ i) ε (κ ≫ eU) z a a' =
      trF (L := L) (fun i => e ≫ φ i) ε (κ ≫ j) z a a' := by
    unfold trF
    refine Finset.prod_congr rfl fun k _ => ?_
    dsimp only
    rw [hw k]
  rw [gen_trans ht (κ ≫ eU) z h1 h1', gen_trans hρ (κ ≫ j) z h2 h2', htr, hv]

theorem existsUnique_gen_extend : ∀ (Y U H HU X : Scheme.{0}) [IsLocallyNoetherian Y] (j : U ⟶ Y) [IsPreimmersion j] [Flat j] [IsDominant j] [QuasiCompact j], Geo.Tor.IsNormalScheme Y → ∀ (p : H ⟶ Y) (e : Y ⟶ H) (jH : HU ⟶ H) (pU : HU ⟶ U) (eU : U ⟶ HU), Smooth p → GeometricallyIntegral p → e ≫ p = 𝟙 _ → IsPullback jH pU p j → eU ≫ jH = j ≫ e → ∀ (L : LB X), L.IsLB → ∀ (I : Type) [Fintype I] (φ : I → (H ⟶ X)) (ε : I → ℤ) (t : LB.Gen (LB.LinComb L (fun i => jH ≫ φ i) ε)) (ρ : LB.Gen (LB.LinComb L (fun i => e ≫ φ i) ε)), t.IsGen → ρ.IsGen → LB.Gen.Corr L _ _ _ _ (LB.pullGen L _ _ t eU) (LB.pullGen L _ _ ρ j) → ∃! c : LB.Gen (LB.LinComb L φ ε), c.IsGen ∧ LB.pullGen L _ _ c jH = t := by
  intro Y U H HU X _ j _ _ _ _ hY p e jH pU eU hsm hgi he hP heU L hL I _ φ ε t ρ ht hρ hc
  haveI := hsm
  haveI := hgi
  have := IsNormalScheme.of_pred hY
  have := isNormalScheme_of_smooth p
  have := LocallyOfFiniteType.isLocallyNoetherian p
  have := IsSchemeTheoreticallyDominant.of_isDominant j
  have hJ := (pullback.fst p j).app_injective
  have hN : (LB.LinComb L φ ε).IsLB := LB.isLB_linComb hL φ ε
  let iso := hP.isoPullback
  have hiso : iso.inv ≫ jH = pullback.fst p j := hP.isoPullback_inv_fst
  have hiso' : iso.hom ≫ pullback.fst p j = jH := hP.isoPullback_hom_fst
  have hisoa : ∀ {W : Scheme.{0}} (g : H ⟶ W), iso.inv ≫ jH ≫ g = pullback.fst p j ≫ g := fun g => by
    rw [← Category.assoc, hiso]
  have hpt : ∀ q, jH (iso.inv q) = pullback.fst p j q := fun q => by
    rw [← Scheme.Hom.comp_apply, hiso]
  have hle : ∀ a, pullback.fst p j ⁻¹ᵁ (LB.LinComb L φ ε).U a ≤
      iso.inv ⁻¹ᵁ LB.wchart L (fun i => jH ≫ φ i) a := fun a q hq =>
    (wchart_comp L jH φ a).ge (show jH (iso.inv q) ∈ LB.wchart L φ a by rw [hpt]; exact hq)
  let τ : ∀ a, Γ(pullback p j, pullback.fst p j ⁻¹ᵁ (LB.LinComb L φ ε).U a)ˣ :=
    fun a => res (hle a) (pullU iso.inv _ (t.s a))
  have hτg : ∀ (Z : Scheme.{0}) (r : Z ⟶ pullback p j) (z : Z) (a),
      pullback.fst p j (r z) ∈ (LB.LinComb L φ ε).U a →
      gm r z _ (τ a) = gm (r ≫ iso.inv) z (LB.wchart L (fun i => jH ≫ φ i) a) (t.s a) :=
    fun Z r z a h => (gm_res r z (hle a) h _).trans (gm_pull r iso.inv z _ (hle a h) _)
  have hτ : Compat (LB.LinComb L φ ε) (pullback.fst p j) τ := fun Z r z a b ha hb => by
    have ha' : (r ≫ iso.inv) z ∈ LB.wchart L (fun i => jH ≫ φ i) a := hle a ha
    have hb' : (r ≫ iso.inv) z ∈ LB.wchart L (fun i => jH ≫ φ i) b := hle b hb
    rw [hτg Z r z a ha, hτg Z r z b hb, gen_trans ht (r ≫ iso.inv) z ha' hb']
    refine congrArg (· * _) (Eq.symm ((gm_linComb L φ ε (r ≫ pullback.fst p j) z a b ha hb).trans ?_))
    rw [trF]
    refine Finset.prod_congr rfl fun k _ => ?_
    simp only [Category.assoc, hisoa]
  have hle' : ∀ a, e ⁻¹ᵁ (LB.LinComb L φ ε).U a ≤ LB.wchart L (fun i => e ≫ φ i) a :=
    fun a => (wchart_comp L e φ a).ge
  let ρ' : ∀ a, Γ(Y, e ⁻¹ᵁ (LB.LinComb L φ ε).U a)ˣ := fun a => res (hle' a) (ρ.s a)
  let eU' : U ⟶ pullback p j := pullback.lift (j ≫ e) (𝟙 U) (by simp [he])
  have w : eU' ≫ pullback.fst p j = j ≫ e := pullback.lift_fst _ _ _
  have hπ : eU' ≫ pullback.snd p j = 𝟙 U := pullback.lift_snd _ _ _
  have hsec : eU ≫ pU = 𝟙 U := by
    rw [← cancel_mono j, Category.id_comp, Category.assoc, ← hP.w, reassoc_of% heU, he,
      Category.comp_id]
  have heU' : eU' ≫ iso.inv = eU := by
    rw [← cancel_mono iso.hom, Category.assoc, Iso.inv_hom_id, Category.comp_id]
    apply pullback.hom_ext
    · rw [w, Category.assoc, hiso', heU]
    · rw [hπ, Category.assoc, hP.isoPullback_hom_snd, hsec]
  have hτρ : ∀ (Z : Scheme.{0}) (κ : Z ⟶ U) (z : Z) (a : I → L.ι),
      e (j (κ z)) ∈ (LB.LinComb L φ ε).U a →
      gm (κ ≫ eU') z (pullback.fst p j ⁻¹ᵁ (LB.LinComb L φ ε).U a) (τ a) =
        gm (κ ≫ j) z (e ⁻¹ᵁ (LB.LinComb L φ ε).U a) (ρ' a) := by
    intro Z κ z a ha
    have hm : pullback.fst p j ((κ ≫ eU') z) ∈ (LB.LinComb L φ ε).U a := by
      rw [← Scheme.Hom.comp_apply, Category.assoc, w]; exact ha
    have e₁ : gm ((κ ≫ eU') ≫ iso.inv) z (LB.wchart L (fun i => jH ≫ φ i) a) (t.s a) =
        gm (κ ≫ eU) z (LB.wchart L (fun i => jH ≫ φ i) a) (t.s a) := by
      rw [Category.assoc, heU']
    exact (hτg Z _ z a hm).trans (e₁.trans ((gm_eq_of_corr hL heU ht hρ hc κ z a ha).trans
      (gm_res (κ ≫ j) z (hle' a) ha _).symm))
  have key : ∀ a, ∀ y ∈ (LB.LinComb L φ ε).U a, Order.coheight y ≤ 1 →
      y ∉ Set.range (pullback.fst p j) →
      ExtAt (pullback.fst p j) ((LB.LinComb L φ ε).U a) (τ a).val y ∧
        ExtAt (pullback.fst p j) ((LB.LinComb L φ ε).U a) ((τ a)⁻¹).val y := fun a y ha h1 hy ↦ by
    refine extAt_of_coheight_eq_one j p he hN w hπ hτ hτρ y
      (le_antisymm (coheight_apply_le_one p h1) (ENat.one_le_iff_ne_zero.2 fun h0 ↦ hy ?_)) a ha
    rw [Scheme.Pullback.range_fst]
    obtain ⟨ξ, hξ, hξy⟩ := exists_specializes_mem_range j (p y)
    exact (Flat.generalizingMap j).stableUnderGeneralization_range
      (show p y ⤳ ξ from Order.coheight_eq_zero.1 h0 hξy) hξ
  choose s hs using fun a ↦ exists_app_eq _ hJ _ _ fun y ha h1 hy ↦ (key a y ha h1 hy).1
  choose s' hs' using fun a ↦ exists_app_eq _ hJ _ _ fun y ha h1 hy ↦ (key a y ha h1 hy).2
  have hm : ∀ a, s a * s' a = 1 := fun a ↦ hJ _ (by
    change ((pullback.fst p j).app _).hom _ = ((pullback.fst p j).app _).hom _
    rw [map_mul, map_one, hs, hs', Units.mul_inv])
  let σ : ∀ a, Γ(H, (LB.LinComb L φ ε).U a)ˣ := fun a ↦ ⟨s a, s' a, hm a, (mul_comm _ _).trans (hm a)⟩
  have hσ : ∀ a, pullU (pullback.fst p j) _ (σ a) = τ a := fun a ↦ Units.ext (hs a)
  have hgen : (⟨σ⟩ : LB.Gen (LB.LinComb L φ ε)).IsGen := fun a b ↦ Units.map_injective
      (f := ((pullback.fst p j).app ((LB.LinComb L φ ε).U a ⊓ (LB.LinComb L φ ε).U b)).hom.toMonoidHom)
      (hJ _) (by
    change pullU _ _ _ = pullU _ _ _
    refine unit_ext fun q hq ↦ ?_
    have := hτ _ (𝟙 _) q a b hq.1 hq.2
    rw [← hσ, ← hσ, gm_pull _ _ q _ hq.1, gm_pull _ _ q _ hq.2] at this
    rw [gm_pull _ _ q _ hq, gm_pull _ _ q _ hq, map_mul, gm_res _ q _ hq, gm_res _ q _ hq]
    exact this)
  have hτc : ∀ c : LB.Gen (LB.LinComb L φ ε), LB.pullGen L _ _ c jH = t → ∀ a,
      pullU (pullback.fst p j) _ (c.s a) = τ a := by
    rintro c rfl a
    refine unit_ext fun q hq ↦ ?_
    rw [gm_pull _ _ q _ hq, hτg _ (𝟙 _) q a hq]
    simp only [Category.id_comp]
    dsimp only [LB.pullGen]
    have h₁ : iso.inv q ∈ LB.wchart L (fun i => jH ≫ φ i) a := hle a hq
    have h₂ : jH (iso.inv q) ∈ LB.wchart L φ a := by rw [hpt]; exact hq
    exact ((gm_res iso.inv q _ h₁ _).trans ((gm_pull iso.inv jH q _ h₂ _).trans (congrArg (fun f => gm f q _ (c.s a)) hiso))).symm
  have hpg : LB.pullGen L _ _ (⟨σ⟩ : LB.Gen (LB.LinComb L φ ε)) jH = t := by
    refine congrArg LB.Gen.mk (funext fun a ↦ unit_ext fun y hy ↦ ?_)
    have hy' : jH y ∈ (LB.LinComb L φ ε).U a := (wchart_comp L jH φ a).le hy
    have h' : pullback.fst p j (iso.hom y) ∈ (LB.LinComb L φ ε).U a := by
      rw [← Scheme.Hom.comp_apply, hiso']; exact hy'
    have e₁ : gm jH y ((LB.LinComb L φ ε).U a) (σ a) =
        gm (𝟙 HU) y (LB.wchart L (fun i => jH ≫ φ i) a) (t.s a) := by
      refine (congrArg (fun f => gm f y ((LB.LinComb L φ ε).U a) (σ a)) hiso'.symm).trans
        ((gm_pull iso.hom _ y _ h' _).symm.trans ?_)
      rw [hσ]
      exact (hτg _ iso.hom y a h').trans (by rw [Iso.hom_inv_id])
    refine Eq.trans ?_ e₁
    dsimp only [LB.pullGen]
    rw [gm_res _ y _ hy, gm_pull _ _ y _ hy', Category.id_comp]
  refine ⟨⟨σ⟩, ⟨hgen, hpg⟩, ?_⟩
  rintro ⟨c⟩ ⟨-, hc'⟩
  refine congrArg LB.Gen.mk (funext fun a ↦ Units.map_injective
    (f := ((pullback.fst p j).app ((LB.LinComb L φ ε).U a)).hom.toMonoidHom) (hJ _) ?_)
  exact (hτc ⟨c⟩ hc' a).trans (hσ a).symm

end GlobalTheory.GenExtendDense
end

section

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne
  GlobalTheory.LocLanglands Module

namespace GlobalTheory.WeilDeligne.IrrDecomp

theorem isIrreducible_of_equiv {G V V' : Type} [Monoid G] [AddCommGroup V] [Module ℂ V]
    [AddCommGroup V'] [Module ℂ V'] {ρ : Representation ℂ G V} {ρ' : Representation ℂ G V'}
    (e : V ≃ₗ[ℂ] V') (he : ∀ g v, e (ρ g v) = ρ' g (e v)) (hρ : ρ.IsIrreducible) :
    ρ'.IsIrreducible := by
  have he' : ∀ g v, e.symm (ρ' g v) = ρ g (e.symm v) := fun g v => by
    rw [e.symm_apply_eq, he, e.apply_symm_apply]
  let F : Subrepresentation ρ ≃o Subrepresentation ρ' :=
    { toFun := fun U => ⟨U.toSubmodule.map (e : V →ₗ[ℂ] V'), fun g v hv => by
        obtain ⟨u, hu, rfl⟩ := hv
        exact ⟨ρ g u, U.apply_mem_toSubmodule g hu, he g u⟩⟩
      invFun := fun U => ⟨U.toSubmodule.map (e.symm : V' →ₗ[ℂ] V), fun g v hv => by
        obtain ⟨u, hu, rfl⟩ := hv
        exact ⟨ρ' g u, U.apply_mem_toSubmodule g hu, he' g u⟩⟩
      left_inv := fun U => by
        apply Subrepresentation.toSubmodule_injective
        ext v
        simp [Submodule.mem_map_equiv]
      right_inv := fun U => by
        apply Subrepresentation.toSubmodule_injective
        ext v
        simp [Submodule.mem_map_equiv]
      map_rel_iff' := by
        intro U U'
        show U.toSubmodule.map (e : V →ₗ[ℂ] V') ≤ U'.toSubmodule.map (e : V →ₗ[ℂ] V') ↔
          U.toSubmodule ≤ U'.toSubmodule
        exact Submodule.map_le_map_iff_of_injective e.injective _ _ }
  haveI : IsSimpleOrder (Subrepresentation ρ) := hρ
  exact F.symm.isSimpleOrder

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

end GlobalTheory.WeilDeligne.IrrDecomp
end
end

section

open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal

theorem _root_.GlobalTheory.T.measurableSet_orbit_exists_measurable_section : ∀ (G X : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] [TopologicalSpace X] [T2Space X] [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X] [MulAction G X] [ContinuousSMul G X] (x₀ : X), MeasurableSet {y : X | ∃ g : G, g • x₀ = y} ∧ ∃ s : X → G, Measurable s ∧ ∀ y, (∃ g : G, g • x₀ = y) → s y • x₀ = y := by
  first | exact @GlobalTheory.OrbitSection.measurableSet_orbit_and_exists_section | exact GlobalTheory.OrbitSection.measurableSet_orbit_and_exists_section | (intros; apply GlobalTheory.OrbitSection.measurableSet_orbit_and_exists_section <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal

theorem _root_.GlobalTheory.T.exists_restricted_product_measure_countable : ∀ (ι : Type) [Countable ι] (V₀ : Type) [MeasurableSpace V₀] (V : ι → Type) [∀ i, MeasurableSpace (V i)] (L : ∀ i, Set (V i)) (m₀ : Measure V₀) (m : ∀ i, Measure (V i)), SigmaFinite m₀ → (∀ i, SigmaFinite (m i)) → (∀ i, MeasurableSet (L i)) → (∀ i, m i (L i) ≠ ∞) → (Summable fun i => |(m i (L i)).toReal - 1|) → ∃ ν : Measure (V₀ × ∀ i, V i), ν {Y | ¬ ∀ᶠ i in Filter.cofinite, Y.2 i ∈ L i} = 0 ∧ ∀ (S : Finset ι) (f₀ : V₀ → ℝ≥0∞) (f : ∀ i, V i → ℝ≥0∞), Measurable f₀ → (∀ i, Measurable (f i)) → ∫⁻ Y in {Y | ∀ i ∉ S, Y.2 i ∈ L i}, f₀ Y.1 * ∏ i ∈ S, f i (Y.2 i) ∂ν = (∫⁻ y, f₀ y ∂m₀) * (∏ i ∈ S, ∫⁻ y, f i y ∂(m i)) * ENNReal.ofReal (∏' i : {i : ι // i ∉ S}, (m i.1 (L i.1)).toReal) := by
  first | exact @GlobalTheory.GaugeEx.AbsProd.exists_restricted_product | exact GlobalTheory.GaugeEx.AbsProd.exists_restricted_product | (intros; apply GlobalTheory.GaugeEx.AbsProd.exists_restricted_product <;> assumption)
end
