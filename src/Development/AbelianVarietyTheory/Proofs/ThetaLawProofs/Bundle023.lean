module

public import Development.AbelianVarietyTheory.Definitions.KeyFormula.LevBasis
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.EqZeroOfSemicharacterMultiplier
public import Development.AbelianVarietyTheory.Definitions.KeyFormula.KeyRuleOneOfKeyFormula
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle006
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle007
public import Development.AbelianVarietyTheory.Statements.ThetaLevelCharacters.MemThetaLevelCharDimZero
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle013
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle018
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.SubsingletonPrimeSpectrum
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TopLePreimageOfValAtNeZero
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.DegProd
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle019
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
import Development.AbelianVarietyTheory.Definitions.KeyFormula.DegProd
import Development.AbelianVarietyTheory.Definitions.KeyFormula.Bundle002

@[expose] public section

section

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.KeyPow

section Scale

variable {R : Type} [CommRing R] {X : Scheme.{0}} (p : X ⟶ Sp R) {L : LB X}

theorem res_constFn {U V : X.Opens} (h : V ≤ U) (a : R) :
    (X.presheaf.map (homOfLE h).op).hom (constFn p U a) = constFn p V a :=
  congrArg (fun k => k.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a))
    (Scheme.Hom.appLE_map p (U := ⊤) (fun _ _ => trivial) (homOfLE h).op)

theorem constFn_mul (U : X.Opens) (a b : R) : constFn p U (a * b) = constFn p U a * constFn p U b := by
  rw [constFn, constFn, constFn, map_mul, map_mul]

theorem constFn_one (U : X.Opens) : constFn p U (1 : R) = 1 := by
  rw [constFn, map_one, map_one]

theorem exists_sec_div {a b : R} (h : a * b = 1) (s : L.Sec) :
    ∃ t : L.Sec, (∀ i, t.f i = constFn p _ b * s.f i) ∧ (∀ i, s.f i = constFn p _ a * t.f i) ∧
      Out.nonzeroLocus s ≤ Out.nonzeroLocus t := by
  have e : ∀ i, s.f i = constFn p _ a * (constFn p _ b * s.f i) := fun i => by
    rw [← _root_.mul_assoc, ← constFn_mul, h, constFn_one, _root_.one_mul]
  refine ⟨⟨fun i => constFn p _ b * s.f i, fun i j => ?_⟩, fun _ => rfl, e, iSup_mono fun i => ?_⟩
  · rw [map_mul, map_mul, res_constFn, res_constFn, s.compat i j, mul_left_comm]
  · conv_lhs => rw [e i, Scheme.basicOpen_mul]
    exact inf_le_right

end Scale

theorem value_at_normalForm :
    ∀ (N : ℕ → ℕ) (g₀ : ℕ) (κ : KeyIn ℂ → ℂˣ) (g : ℕ) (a b : Fin g → ℂ), g₀ ≤ g → GlobalTheory.KeyPow.ClauseH ℂ N g₀ κ → (∀ (x : KeyIn ℂ) (h : x.P.g = g) (τ : Matrix (Fin x.P.g) (Fin x.P.g) ℂ), GlobalTheory.KeyPow.NormalAt x τ 1 (fun i => a (i.cast h)) (fun i => b (i.cast h)) 1 → κ x = 1) → ∀ (x : KeyIn ℂ) (h : x.P.g = g) (τ M : Matrix (Fin x.P.g) (Fin x.P.g) ℂ) (c : ℂ), c ≠ 0 → M.det ≠ 0 → GlobalTheory.KeyPow.NormalAt x τ M (fun i => a (i.cast h)) (fun i => b (i.cast h)) c → (κ x : ℂ) = (M.det ^ 4 / c ^ 8) ^ N g := by
  intro N g₀ κ g a b hg₀ hH hN x h τ M c hc hM hx
  obtain ⟨P, hg, rig, hr, th, hth, v, hv⟩ := x
  dsimp only at h τ M
  subst h
  obtain ⟨u, h₁, h₂, h₃, h₄, h₅, h₆⟩ := hx
  haveI := P.isAb.comm
  obtain ⟨ex, tan, comp, sgl, bas⟩ := GlobalTheory.LieComb.lieComb_algebra ℂ P.A P.g v hv.1
  choose v₀ hv₀ using fun i => (ex (M⁻¹ i)).exists
  have hb₀ : IsLieBasis v₀ := (bas M⁻¹ v₀ hv hv₀).2 (Matrix.isUnit_nonsing_inv_det M hM.isUnit)
  obtain ⟨ex₀, -, -, -, -⟩ := GlobalTheory.LieComb.lieComb_algebra ℂ P.A P.g v₀ hb₀.1
  have hMv : ∀ i, IsLieComb (M i) v₀ (v i) := fun i => by
    obtain ⟨w, hw⟩ := (ex₀ (M i)).exists
    have h1 := comp _ (fun i => M⁻¹ i) v₀ (M i) w hv₀ hw
    have e : ∑ j, M i j • M⁻¹ j = Pi.single i 1 := by
      rw [← Matrix.vecMul_eq_sum]
      refine (congrFun (Matrix.mul_nonsing_inv M hM.isUnit) i).trans ?_
      simpa using smul_one_row (1 : ℂ) i
    rw [e] at h1
    rwa [(ex _).unique (sgl i) h1]
  obtain ⟨th₀, e₀, e₁, hle⟩ := exists_sec_div P.A.hom (mul_inv_cancel₀ hc) th
  have hth₀ : ∀ s : Sp ℂ, ∃ y : P.A.left, P.A.hom y = s ∧ y ∈ Out.nonzeroLocus th₀ :=
    fun s => (hth s).imp fun y hy => ⟨hy.1, hle hy.2⟩
  have h0 : κ ⟨P, hg, rig, hr, th₀, hth₀, v₀, hb₀⟩ = 1 := by
    refine hN ⟨P, hg, rig, hr, th₀, hth₀, v₀, hb₀⟩ rfl τ ⟨u, h₁, h₂, h₃, h₄, ?_, ?_⟩
    · intro i z hz
      have e := h₅ i z hz
      refine ((congrArg (valAt' _ _) (e₀ i)).trans (valAt'_mul _ _ _ _)).trans ?_
      rw [valAt'_constFn _ _ (Over.w (u.ex z)) _ _ hz]
      refine (congrArg (c⁻¹ * ·) e).trans ?_
      beta_reduce
      rw [_root_.one_mul, ← _root_.mul_assoc, inv_mul_cancel_left₀ hc]
    · intro i
      have h1 := GlobalTheory.UnifDifferential.isDiff_of_isLieComb P.A P.L P.g P.g u _ v _ _ hv.1 h₆ (hv₀ i)
      have e : ∑ j, M⁻¹ i j • ((2 * Real.pi * Complex.I : ℂ)⁻¹ • M j) =
          (2 * Real.pi * Complex.I : ℂ)⁻¹ • (1 : Matrix (Fin P.g) (Fin P.g) ℂ) i := by
        simp only [smul_comm (M⁻¹ i _) (2 * Real.pi * Complex.I : ℂ)⁻¹]
        rw [← Finset.smul_sum, ← Matrix.vecMul_eq_sum, ← Matrix.nonsing_inv_mul M hM.isUnit]
        rfl
      rwa [e] at h1
  have h1 := hH P hg rig hr _ hth₀ v₀ hb₀ th hth v hv c M hg₀ e₁ hMv
  rw [h0, Units.val_one, _root_.mul_one] at h1
  rw [div_pow, ← pow_mul, ← pow_mul, eq_div_iff (pow_ne_zero _ hc), mul_comm]
  exact h1

end GlobalTheory.KeyPow
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.KeyPow GlobalTheory.KeyKa
open GlobalTheory.KeyEq

noncomputable section
namespace GlobalTheory.KeyEq

theorem normalAt_scale :
    ∀ (P : Out.PolAV (Sp ℂ)) (hg rig hr th hth v hv th' hth' v' hv') (a : ℂ) (N : Matrix (Fin P.g) (Fin P.g) ℂ), (∀ i, LB.Sec.f th' i = constFn P.A.hom _ a * LB.Sec.f th i) → (∀ i, IsLieComb (N i) v (v' i)) → a ≠ 0 ∧ N.det ≠ 0 ∧ ∀ (τ M : Matrix (Fin P.g) (Fin P.g) ℂ) (α β : Fin P.g → ℂ) (c : ℂ), NormalAt ⟨P, hg, rig, hr, th, hth, v, hv⟩ τ M α β c → NormalAt ⟨P, hg, rig, hr, th', hth', v', hv'⟩ τ (N * M) α β (a * c) := by
  intro P hg rig hr th hth v hv th' hth' v' hv' a N ha hN
  haveI := P.isAb.comm
  obtain ⟨-, -, -, -, bas⟩ := GlobalTheory.LieComb.lieComb_algebra ℂ P.A P.g v hv.1
  refine ⟨?_, ((bas N v' hv hN).1 hv').ne_zero, ?_⟩
  · rintro rfl
    obtain ⟨y, -, hy⟩ := hth' (IsLocalRing.closedPoint ℂ)
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hy
    rw [ha i, constFn, map_zero, map_zero, zero_mul, Scheme.basicOpen_zero] at hi
    exact hi
  · rintro τ M α β c ⟨u, h₁, h₂, h₃, h₄, h₅, h₆⟩
    refine ⟨u, h₁, h₂, h₃, h₄, ?_, ?_⟩
    · intro i z hz
      have e := h₅ i z hz
      refine ((congrArg (valAt' _ _) (ha i)).trans (valAt'_mul _ _ _ _)).trans ?_
      rw [valAt'_constFn _ _ (Over.w (u.ex z)) _ _ hz]
      refine (congrArg (a * ·) e).trans ?_
      beta_reduce
      simp only [_root_.mul_assoc]
    · intro i
      have h1 := GlobalTheory.UnifDifferential.isDiff_of_isLieComb P.A P.L P.g P.g u _ v _ _ hv.1 h₆ (hN i)
      have e : ∑ j, N i j • ((2 * Real.pi * Complex.I : ℂ)⁻¹ • M j) =
          (2 * Real.pi * Complex.I : ℂ)⁻¹ • (N * M) i := by
        simp only [smul_comm (N i _) (2 * Real.pi * Complex.I : ℂ)⁻¹]
        rw [← Finset.smul_sum, ← Matrix.vecMul_eq_sum]
        rfl
      rwa [e] at h1

end GlobalTheory.KeyEq
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.KeyPow GlobalTheory.KeyKa
open GlobalTheory.KeyEq

noncomputable section
namespace GlobalTheory.KeyEq

theorem det_ne_zero_of_normalAt (hU : ThetaUnifAV) (x : KeyIn ℂ) {τ M : Matrix (Fin x.P.g) (Fin x.P.g) ℂ}
    {a b : Fin x.P.g → ℂ} {c : ℂ} (h : NormalAt x τ M a b c) : M.det ≠ 0 := by
  obtain ⟨u, -, -, -, -, -, h₆⟩ := h
  obtain ⟨u₀, -, -, -, -, -, -, hd, -⟩ := hU x.P x.rig x.rig_gen
  have := x.P.isAb.comm
  obtain ⟨hex, htan, -⟩ := LieComb.lieComb_algebra ℂ x.P.A x.P.g x.v x.basis.1
  intro h0
  obtain ⟨d, hd0, hdM⟩ := Matrix.exists_vecMul_eq_zero_iff.2 h0
  have key : ∀ (e : Fin x.P.g → ℂ) (w), Matrix.vecMul e M = 0 → IsLieComb e x.v w → u₀.IsDiff 0 w := by
    intro e w he hw
    have h1 := UnifDifferential.isDiff_of_isLieComb _ _ _ _ u _ x.v e w x.basis.1 h₆ hw
    have e1 : ∑ j, e j • (2 * Real.pi * Complex.I : ℂ)⁻¹ • M j =
        (2 * Real.pi * Complex.I : ℂ)⁻¹ • Matrix.vecMul e M := by
      rw [Matrix.vecMul_eq_sum, Finset.smul_sum]
      exact Finset.sum_congr rfl fun j _ => smul_comm _ _ _
    rw [e1, he, smul_zero] at h1
    intro U hU' f
    rw [h1 U hU' f, map_zero, map_zero]
  obtain ⟨w, hw⟩ := (hex d).exists
  obtain ⟨w', hw'⟩ := (hex 0).exists
  have hww : w = w' := (hd 0).unique ⟨htan _ _ hw, key _ _ hdM hw⟩
    ⟨htan _ _ hw', key _ _ (Matrix.zero_vecMul M) hw'⟩
  subst hww
  exact hd0 ((x.basis.2 w (htan _ _ hw)).unique hw hw')

end GlobalTheory.KeyEq
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyPow GlobalTheory.KeyKa
noncomputable section
namespace GlobalTheory.KeyKa

theorem normalAt_iff_wit : ∀ (g : ℕ) (x : KeyIn ℂ) (h : x.P.g = g) (τ : Matrix (Fin x.P.g) (Fin x.P.g) ℂ) (a b : Fin g → ℂ), NormalAt x τ 1 (fun i => a (i.cast h)) (fun i => b (i.cast h)) 1 ↔ ∃ u : HolUnif x.P.A x.P.L g, Wit x h u (τ.submatrix (Fin.cast h.symm) (Fin.cast h.symm)) a b := by
  intro g x h τ a b
  subst h
  exact normalAt_one_iff ..

end GlobalTheory.KeyKa
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyPow GlobalTheory.KeyKa

noncomputable section
namespace GlobalTheory.KeyKa.LevelBasis

section Real
open ReciprocityTheory.PTheta Matrix

theorem isLevel_iff {g : ℕ} (τ : Matrix (Fin g) (Fin g) ℂ) (a b : Fin g → ℝ) (l : ℕ) (F : (Fin g → ℂ) → ℂ) :
    IsLevel τ (ofRealVec a) (ofRealVec b) l F ↔ F ∈ thetaLevelChar a b l τ := by
  have key : ∀ (m n : Fin g → ℤ) (z : Fin g → ℂ),
      Complex.exp (2 * Real.pi * Complex.I * (ofRealVec a ⬝ᵥ (fun i => (m i : ℂ)) - ofRealVec b ⬝ᵥ (fun i => (n i : ℂ)) -
        ((fun i => (n i : ℂ)) ⬝ᵥ τ.mulVec (fun i => (n i : ℂ))) / 2 - (fun i => (n i : ℂ)) ⬝ᵥ z)) ^ l =
      eC ((l : ℂ) * (ofRealVec a ⬝ᵥ ofIntVec m - ofRealVec b ⬝ᵥ ofIntVec n)) *
        eC (-(l : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) / 2 + ofIntVec n ⬝ᵥ z)) := by
    intro m n z
    unfold eC
    rw [← Complex.exp_nat_mul, ← Complex.exp_add]
    congr 1
    unfold ofIntVec
    ring
  have e : ∀ (m n : Fin g → ℤ) (z : Fin g → ℂ),
      z + ((fun i => (m i : ℂ)) + τ.mulVec (fun i => (n i : ℂ))) = z + τ *ᵥ ofIntVec n + ofIntVec m := by
    intro m n z
    unfold ofIntVec
    abel
  rw [mem_thetaLevelChar]
  refine and_congr Iff.rfl ⟨fun h n m z => ?_, fun h m n z => ?_⟩
  · rw [← key, ← e]; exact h m n z
  · rw [key, e]; exact h n m z

theorem holFam_levelTheta {g : ℕ} (a b : Fin g → ℝ) {l : ℕ} (hl : 0 < l) (c : Fin g → ℤ) :
    HolFam (Key.phDom g) (fun p => levelTheta a b l (per p) c) := by
  have H := thetaHolo_of_domainOpen_of_mTest siegelSubDomain_and_domainOpen.2 thetaMTest_holds (Fin g)
    ((fun i => (c i : ℝ) / l) + a) ((l : ℝ) • b)
  have hd : Differentiable ℂ (fun q : (Fin g → Fin g → ℂ) × (Fin g → ℂ) =>
      (((l : ℂ) • q.2, fun i j => (l : ℂ) * ((1 / 2 : ℂ) * (q.1 i j + q.1 j i))) :
        (Fin g → ℂ) × (Fin g → Fin g → ℂ))) := by
    fun_prop
  refine (H.comp hd.differentiableOn fun q hq => ?_).congr fun q _ => rfl
  exact siegelSubDomain_and_domainOpen.1 _ (smul_mem_siegelH hq.1 hl)

theorem exists_levBasis_real (g : ℕ) (a b : Fin g → ℝ) {l : ℕ} (hl : 0 < l) :
    ∃ Th : Fin (l ^ g) → (Fin g → Fin g → ℂ) → (Fin g → ℂ) → ℂ, LevBasis (ofRealVec a) (ofRealVec b) l Th := by
  let e : Fin (l ^ g) ≃ (Fin g → Fin l) := finFunctionFinEquiv.symm
  let r : Fin (l ^ g) → Fin g → ℤ := fun k i => ((e k i : ℕ) : ℤ)
  have hr : Function.Bijective fun k i => (r k i : ZMod l) := (@GlobalTheory.bijective_fin_zmod (Fin g) l hl).comp e.bijective
  refine ⟨fun k p => levelTheta a b l (per p) (r k), fun k => holFam_levelTheta a b hl _, fun p hp =>
    ⟨fun k => (isLevel_iff _ _ _ _ _).2 (levelTheta_mem hp hl _), fun F hF => ?_⟩⟩
  let B := thetaLevelCharBasis a b (τ := per p) hp hl hr
  have hF' := (isLevel_iff _ _ _ _ _).1 hF
  have hB : ∀ (c : Fin (l ^ g) → ℂ) z, ((∑ k, c k • B k : thetaLevelChar a b l (per p)) : (Fin g → ℂ) → ℂ) z =
      ∑ k, c k * levelTheta a b l (per p) (r k) z := fun c z => by
    rw [Submodule.coe_sum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul]
    exact congrArg _ (congrFun (thetaLevelCharBasis_apply (τ := per p) hp hl hr k) z)
  refine ⟨fun k => B.repr ⟨F, hF'⟩ k, fun z => ?_, fun c hc => ?_⟩
  · rw [← hB, B.sum_repr]
  · have : (⟨F, hF'⟩ : thetaLevelChar a b l (per p)) = ∑ k, c k • B k := Subtype.ext (funext fun z => by
      rw [hB]; exact hc z)
    funext k
    rw [this, B.repr_sum_self]

end Real

theorem exists_levBasis : ∀ (g : ℕ) (a b : Fin g → ℂ) (l : ℕ), charHalf g a b → 1 ≤ l → ∃ Th : Fin (l ^ g) → (Fin g → Fin g → ℂ) → (Fin g → ℂ) → ℂ, LevBasis a b l Th := by
  intro g a b l h hl
  have := exists_levBasis_real g (fun i => (a i).re) (fun i => (b i).re) (l := l) hl
  rwa [TorusAlg.ofRealVec_re h.1, TorusAlg.ofRealVec_re h.2] at this

end GlobalTheory.KeyKa.LevelBasis
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa


theorem _root_.GlobalTheory.T.pullbackSectionsSpanTwisted_of_indep_span : ∀ (X Y T : Scheme.{0}) (L : LB X) (t : ℤ) (N : ℕ) (b : Fin N → LB.Sec (pw L t)) (p₁ : Y ⟶ T) (p₂ : Y ⟶ X), L.IsLB → (∀ W : T.Opens, GlobalTheory.RelBasis.IndepOn b p₁ p₂ W ∧ GlobalTheory.RelBasis.SpanOn b p₁ p₂ W) → GlobalTheory.RelBasis.BoxSpan b p₁ p₂ := by
  first | exact @GlobalTheory.RelBasis.boxSpan_of_indep_span | exact GlobalTheory.RelBasis.boxSpan_of_indep_span | (intros; apply GlobalTheory.RelBasis.boxSpan_of_indep_span <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa


theorem _root_.GlobalTheory.T.boxProducts_span_external_powers_of_boxSpan : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) (L : LB A.left) (t : ℤ) (N : ℕ) (b : Fin N → LB.Sec (pw L t)), L.IsLB → (∀ T : Over (Sp R), GlobalTheory.RelBasis.BoxSpan b (snd A T).left (fst A T).left) → ∀ (n : ℕ) (s : LB.Sec (LB.LinComb L (K := Fin n) (fun c => (Out.powPr A c).left) (fun _ => t))), ∃ q : (Fin n → Fin N) → R, ∀ (Z : Scheme.{0}) (r : Z ⟶ (Out.powObj A n).left) (z : Z) J, Good L z J → sval s r z J = ∑ I, gs r z ⊤ (cst (Out.powObj A n).hom ⊤ (q I)) * ∏ c, gs (r ≫ (Out.powPr A c).left) z (L.U (J (r ≫ (Out.powPr A c).left))) ((b (I c)).f (J (r ≫ (Out.powPr A c).left))) := by
  first | exact @GlobalTheory.PowSpan.boxProducts_span_of_boxSpan | exact GlobalTheory.PowSpan.boxProducts_span_of_boxSpan | (intros; apply GlobalTheory.PowSpan.boxProducts_span_of_boxSpan <;> assumption)
end
