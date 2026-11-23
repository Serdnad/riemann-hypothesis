module

public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.PermutesRefl
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PrincipalRootReZeroImSq
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.NormConst
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle009
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle005
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle062
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle054

public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsUniqueScaledBaseChangeFibreSection
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle059
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle036
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.SymplecticCharacters.InversionStatement
public import Mathlib.NumberTheory.LegendreSymbol.ZModChar
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.EqZeroOfSemicharacterMultiplier
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ChangeOfNormalisation
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CmUnitPowFourIdempotentModEight
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.DifferentiableOnLeftInverse
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle014
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle056
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle019
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle060
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Mathlib.Tactic.ReduceModChar
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle003

@[expose] public section

section

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors

theorem _root_.GlobalTheory.T.thetaPoints_frame_ratio : Out.SecTwistSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1)) (r : ℕ) (M : ModelsOf F r) (k : Fin F.n) (T : ThetaData e F M k), ∀ b ∈ T.co ⁻¹' (M.X k).dom, ∀ (κ : ℂ) (t₀ : (CAt σ)ˣ) (y y' : FrPt Xo c (CAt σ)), IsThetaPt T b κ y → IsThetaPt T b (toC (t₀ : CAt σ) * κ) y' → FrBor (fun i => Option.elim i t₀ (fun _ => 1)) y y' := by
  first | exact @GlobalTheory.frBor_of_isThetaPt | exact GlobalTheory.frBor_of_isThetaPt | (intros; apply GlobalTheory.frBor_of_isThetaPt <;> assumption)
end

section

open NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PureType

namespace GlobalTheory.CompRat

theorem exists_isSplit_of_splitLat (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H)
    (g : ℕ) (ty : Fin g → (E →+* ℂ)) (hty : IsTypeFn H D.p D.q ty) (hD : SplitLat D) :
    ∃ (P : D.La →+ (Fin g → ℂ)) (hP : IsPeriod D ty P), IsSplit hP := by
  obtain ⟨Lp, Lm, hs, ho, -, -, hp, hm⟩ := hD
  have two : ∀ m, (D.EF (H.rt • m) m : ℝ) = 2 * D.EF (H.w0 • m) m := fun m => by
    have : D.EF ((2 * H.w0) • m) m = D.EF ((1 + H.rt) • m) m := by rw [H.two_weight_eq_one_add_root]
    rw [two_mul, add_smul, add_smul, one_smul, map_add (f := _), map_add (f := _), LinearMap.add_apply, LinearMap.add_apply,
      D.alt] at this
    have h : D.EF (H.rt • m) m = 2 * D.EF (H.w0 • m) m := by linarith
    exact_mod_cast h
  obtain ⟨P, hP, k₁, k₂⟩ := GlobalTheory.CM.FamCompare.exists_period D Lp Lm
    (fun z => ⟨1, one_pos, hs ▸ Submodule.mem_top⟩) ho
    (fun x hx => by
      by_cases h : x = 0
      · simp [h]
      · have := hp x hx h
        rw [two] at this
        linarith)
    (fun x hx => by
      by_cases h : x = 0
      · simp [h]
      · have := hm x hx h
        rw [two] at this
        linarith) hty
  exact ⟨P, hP, top_le_iff.1 (hs ▸ sup_le_sup k₁ k₂)⟩

end GlobalTheory.CompRat
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.PureType GlobalTheory.CompRat
open scoped CategoryTheory.Obj

namespace GlobalTheory.CompRat.Acts

theorem corr (ω : ℂ) (f : ℤ × ℤ → ℂ) (hf : ∀ s, f s = s.1 + s.2 * ω) (R : ℂ → ℂ → Prop)
    (tot : ∀ z, ∃ z', R z z') (sur : ∀ z', ∃ z, R z z')
    (add : ∀ z z' y y', R z z' → R y y' → R (z + y) (z' + y'))
    (om : ∀ z z', R z z' → R (ω * z) (ω * z'))
    (iff : ∀ z z' y y', R z z' → R y y' → ((∃ a, z - y = f a) ↔ ∃ a, z' - y' = f a))
    (rsp : ∀ z z' y', R z z' → (∃ a, z' - y' = f a) → R z y') (n : ℕ) (hn : 0 < n) :
    (∃ s, ∀ a, R (f a / n) (f s * f a / n)) ∧
      ∀ s, (∀ a, R (f a / n) (f s * f a / n)) → ∃ s' a, f s' * f s = 1 + n * f a := by
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have f0 : f (0, 0) = 0 := by simp [hf]
  have f1 : f (1, 0) = 1 := by simp [hf]
  have h0 : R 0 0 := by
    obtain ⟨z', h⟩ := tot 0
    obtain ⟨a, ha⟩ := (iff _ _ _ _ (add _ _ _ _ h h) h).1 ⟨(0, 0), by simp [f0]⟩
    exact rsp _ _ _ h ⟨a, by rw [← ha]; ring⟩
  have neg : ∀ z z', R z z' → R (-z) (-z') := by
    intro z z' h
    obtain ⟨y, hy⟩ := tot (-z)
    obtain ⟨a, ha⟩ := (iff _ _ _ _ (add _ _ _ _ h hy) h0).1 ⟨(0, 0), by simp [f0]⟩
    exact rsp _ _ _ hy ⟨a, by rw [← ha]; ring⟩
  have int : ∀ (m : ℤ) z z', R z z' → R (m * z) (m * z') := by
    intro m z z' h
    induction m using Int.induction_on with
    | zero => simpa using h0
    | succ k ih =>
      have := add _ _ _ _ ih h
      convert this using 1 <;> push_cast <;> ring
    | pred k ih =>
      have := add _ _ _ _ ih (neg _ _ h)
      convert this using 1 <;> push_cast <;> ring
  have mul : ∀ a z z', R z z' → R (f a * z) (f a * z') := by
    intro a z z' h
    have := add _ _ _ _ (int a.1 _ _ h) (int a.2 _ _ (om _ _ h))
    convert this using 1 <;> rw [hf] <;> ring
  constructor
  · obtain ⟨z', h⟩ := tot (1 / n)
    obtain ⟨s, hs⟩ := (iff _ _ _ _ (int n _ _ h) h0).1 ⟨(1, 0), by rw [f1]; push_cast; field_simp; ring⟩
    refine ⟨s, fun a => ?_⟩
    have := mul a _ _ h
    convert this using 1
    · ring
    · rw [← hs]; push_cast; field_simp; ring
  · intro s hs
    obtain ⟨z, h⟩ := sur (1 / n)
    obtain ⟨s', hs'⟩ := (iff _ _ _ _ (int n _ _ h) h0).2 ⟨(1, 0), by rw [f1]; push_cast; field_simp; ring⟩
    obtain ⟨a, ha⟩ := (iff _ _ _ _ (hs s') h).1 ⟨(0, 0), by rw [f0, ← hs']; push_cast; field_simp; ring⟩
    refine ⟨s', a, ?_⟩
    rw [← ha]; field_simp; ring

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem spMap_symm (τ : ℂ ≃+* ℂ) : spMap (τ.symm : ℂ →+* ℂ) ≫ spMap (τ : ℂ →+* ℂ) = 𝟙 _ := by
  show Spec.map _ ≫ Spec.map _ = 𝟙 _
  rw [← Spec.map_comp, ← Spec.map_id]
  congr 1
  ext x; simp

theorem pt_over (C : Curve H) (z : ℂ) : C.pt z ≫ C.P.A.hom = 𝟙 _ := Over.w (C.u.ex fun _ => C.c * z)

theorem pt_add (C : Curve H) {f : Sp ℂ ⟶ Sp ℂ} {io : C.P.A.left ⟶ C.P.A.left}
    (h : IsGrpPullback C.P.A C.P.A f io) {z z' y y' : ℂ} (hz : C.pt z' ≫ io = f ≫ C.pt z)
    (hy : C.pt y' ≫ io = f ≫ C.pt y) : C.pt (z' + y') ≫ io = f ≫ C.pt (z + y) := by
  have e : ∀ a b, C.pt (a + b) = (C.u.ex (fun _ => C.c * a) * C.u.ex (fun _ => C.c * b)).left := by
    intro a b
    rw [← C.u.ex_add, Curve.pt]
    congr 2
    funext _; simp [mul_add]
  let U : Over.mk ((𝟙_ (Over (Sp ℂ))).hom ≫ f) ⟶ 𝟙_ (Over (Sp ℂ)) := Over.homMk f (by simp)
  have := h.2 _ (C.u.ex fun _ => C.c * z') (C.u.ex fun _ => C.c * y') (U ≫ C.u.ex fun _ => C.c * z)
    (U ≫ C.u.ex fun _ => C.c * y) hz.symm hy.symm
  rw [← MonObj.comp_mul] at this
  rw [e, e]
  exact this.symm

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (C : Curve H), ∀ τ : ℂ ≃+* ℂ, τ H.rt0 = H.rt0 → ∀ io : C.P.A.left ⟶ C.P.A.left, IsGrpPullback C.P.A C.P.A (spMap (τ : ℂ →+* ℂ)) io → ∀ n : ℕ, 0 < n → (∃ s, C.ActsBy τ io n s) ∧ ∀ s, C.ActsBy τ io n s → (∃ s' a, wC H s' * wC H s = 1 + n * wC H a) ∧ ∀ m : ℕ, m ∣ n → C.ActsBy τ io m s := by
  intro E _ _ _ H C τ hτ io h n hn
  obtain ⟨W, -, hW, hker, hon, hcomm⟩ := GlobalTheory.T.exists_cmEndomorphism_comm_conjugation E H C
  have hc := hcomm τ hτ io h
  have key := corr (wC H (0, 1)) (wC H) (fun s => by simp [wC])
    (fun z z' => C.pt z' ≫ io = spMap (τ : ℂ →+* ℂ) ≫ C.pt z)
    (fun z => by
      have w : (spMap (τ : ℂ →+* ℂ) ≫ C.pt z) ≫ C.P.A.hom = 𝟙 _ ≫ spMap (τ : ℂ →+* ℂ) := by
        rw [Category.assoc, pt_over]; simp
      obtain ⟨z', hz⟩ := hon (h.1.lift _ _ w) (h.1.lift_snd _ _ w)
      exact ⟨z', by rw [hz, h.1.lift_fst]⟩)
    (fun z' => by
      obtain ⟨z, hz⟩ := hon (spMap (τ.symm : ℂ →+* ℂ) ≫ C.pt z' ≫ io) (by
        rw [Category.assoc, Category.assoc, h.1.w, ← Category.assoc (C.pt z'), pt_over, Category.id_comp,
          spMap_symm])
      refine ⟨z, ?_⟩
      have := spMap_symm τ.symm
      rw [RingEquiv.symm_symm] at this
      rw [hz, ← Category.assoc, this, Category.id_comp])
    (fun z z' y y' hz hy => pt_add C h hz hy)
    (fun z z' hz => by
      rw [← hW, ← hW, Category.assoc, hc, ← Category.assoc, hz, Category.assoc])
    (fun z z' y y' hz hy => by
      rw [← hker, ← hker]
      constructor
      · intro e
        apply h.1.hom_ext
        · rw [hz, hy, e]
        · rw [pt_over, pt_over]
      · intro e
        have e' : spMap (τ : ℂ →+* ℂ) ≫ C.pt z = spMap (τ : ℂ →+* ℂ) ≫ C.pt y := by rw [← hz, ← hy, e]
        have := congrArg (spMap (τ.symm : ℂ →+* ℂ) ≫ ·) e'
        simpa only [← Category.assoc, spMap_symm, Category.id_comp] using this)
    (fun z z' y' hz e => by rw [← (hker _ _).2 e]; exact hz) n hn
  refine ⟨key.1.imp fun s hs => ⟨h, hs⟩, fun s hs => ⟨key.2 s hs.2, ?_⟩⟩
  rintro m ⟨k, rfl⟩
  refine ⟨h, fun a => ?_⟩
  have hk : (k : ℂ) ≠ 0 := by
    rintro hk
    have : k = 0 := by exact_mod_cast hk
    simp [this] at hn
  have e : wC H (k * a.1, k * a.2) = k * wC H a := by simp [wC]; ring
  have := hs.2 (k * a.1, k * a.2)
  rw [e] at this
  have hm : (m : ℂ) ≠ 0 := by
    rintro hk
    have : m = 0 := by exact_mod_cast hk
    simp [this] at hn
  have e1 : wC H s * (k * wC H a) / ((m * k : ℕ) : ℂ) = wC H s * wC H a / m := by push_cast; field_simp
  have e2 : (k * wC H a) / ((m * k : ℕ) : ℂ) = wC H a / m := by push_cast; field_simp
  rwa [e1, e2] at this

end GlobalTheory.CompRat.Acts
end

section

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors

namespace GlobalTheory.FrameUnif.ThetaPtEx

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l}

theorem exists_chart_top {X : Scheme.{0}} {L : LB X} (hL : L.IsLB) (p : Sp ℂ ⟶ X) :
    ∃ j, ⊤ ≤ p ⁻¹ᵁ L.U j := by
  obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1
    (hL.cover.ge (Set.mem_univ (p (default : PrimeSpectrum ℂ))))
  refine ⟨j, fun q _ => ?_⟩
  obtain rfl : q = (default : PrimeSpectrum ℂ) := Subsingleton.elim (α := PrimeSpectrum ℂ) _ _
  exact hj

theorem exists_gen (hT : Out.SecTwistSt) (y : Sp ℂ ⟶ Xo.X) {Z : Type} (ex : Z → (Over.mk y ⟶ Xo.univ.t.G))
    (θ : Z → ℂ) (fr : Xo.univ.t.PP.L.ι → Z → ℂ) (κ : ℂ) (hκ : κ ≠ 0) (hθ : ∃ z, θ z ≠ 0)
    (hfr : ∀ j z, ⊤ ≤ (ex z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j → fr j z ≠ 0)
    (s : (Xo.univ.t.PP.L.pull (pullback.fst Xo.univ.t.G.hom y)).Sec)
    (hs : ∀ j z (x : Sp ℂ ⟶ pullback Xo.univ.t.G.hom y),
        x ≫ pullback.fst _ _ = (ex z).left → x ≫ pullback.snd _ _ = 𝟙 _ →
        ⊤ ≤ (ex z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
        valAt' x ((Xo.univ.t.PP.L.pull (pullback.fst Xo.univ.t.G.hom y)).U (fun _ => j))
          (s.f (fun _ => j)) = θ z * fr j z) :
    ∃ t : LB.Sec (PPx y), SecGen y t ∧
      ∀ j z (pt : Sp ℂ ⟶ Gx y), pt ≫ gxFst y = (ex z).left → pt ≫ gxSnd y = 𝟙 (Sp ℂ) →
        ⊤ ≤ (ex z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
        valAt' pt ((PPx y).U (fun _ => j)) (t.f (fun _ => j)) = κ * θ z * fr j z := by
  obtain ⟨s', hs'⟩ := GlobalTheory.T.exists_fibreSection_other_model_same_values E H Dw l Xo y s
  have hw : ∀ z, (ex z).left ≫ Xo.univ.t.G.hom = 𝟙 (Sp ℂ) ≫ y := fun z =>
    (Over.w (ex z)).trans (Category.id_comp y).symm
  have key : ∀ j z (pt : Sp ℂ ⟶ Gx y), pt ≫ gxFst y = (ex z).left → pt ≫ gxSnd y = 𝟙 (Sp ℂ) →
      ⊤ ≤ (ex z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
      valAt' pt ((PPx y).U (fun _ => j)) ((SecPull.scalSec y κ s').f (fun _ => j)) = κ * θ z * fr j z := by
    intro j z pt h1 h2 h3
    have e1 := (GlobalTheory.T.sec_values_complex_fibre_abelianScheme hT E H Dw l Xo y s').1 κ (fun _ => j) pt h2
    have e2 := hs' j pt (pullback.lift (ex z).left (𝟙 _) (hw z)) ((pullback.lift_fst _ _ _).trans h1.symm)
      (pullback.lift_snd _ _ _) h2
    have e3 := hs j z (pullback.lift (ex z).left (𝟙 _) (hw z)) (pullback.lift_fst _ _ _)
      (pullback.lift_snd _ _ _) h3
    refine e1.trans ?_
    rw [e2, e3, mul_assoc]
  refine ⟨SecPull.scalSec y κ s', ?_, key⟩
  obtain ⟨z, hz⟩ := hθ
  obtain ⟨j, hj⟩ := exists_chart_top Xo.univ.t.PP.isLB (ex z).left
  let pt : Sp ℂ ⟶ Gx y := pullback.lift (f := (Over.mk y).hom) (g := Xo.univ.t.G.hom) (𝟙 _) (ex z).left (hw z).symm
  have h1 : pt ≫ gxFst y = (ex z).left := pullback.lift_snd _ _ _
  have h2 : pt ≫ gxSnd y = 𝟙 (Sp ℂ) := pullback.lift_fst _ _ _
  refine (GlobalTheory.T.sec_values_complex_fibre_abelianScheme hT E H Dw l Xo y _).2.1.2 ⟨fun _ => j, pt, h2, ?_⟩
  rw [key j z pt h1 h2 hj]
  exact mul_ne_zero (mul_ne_zero hκ hz) (hfr j z hj)

theorem exists_thetaPt : Out.SecTwistSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1)) (r : ℕ) (M : ModelsOf F r) (k : Fin F.n) (T : ThetaData e F M k), ∀ b ∈ T.co ⁻¹' (M.X k).dom, ∀ κ : ℂ, κ ≠ 0 → ∃ y : FrPt Xo c (CAt σ), IsThetaPt T b κ y := by
  intro hT E _ _ _ H Dw l Xo c σ g e F r M k T b hb κ hκ
  have hP := T.isPer _ hb
  obtain ⟨u, hu, htan, heig, hbas⟩ := GlobalTheory.T.exists_tangent_eigenbasis_exponential E H Dw l Xo c σ g e F k _ hP
  obtain ⟨s, hs⟩ := T.fr_sec b hb
  obtain ⟨hdet, hsym, hpos, -⟩ := T.norm b hb
  obtain ⟨w, hw⟩ := ((GlobalTheory.T.thetaChar_half_differentiable_ne_zero_families g T.c₁ T.c₂ T.half₁ T.half₂).1 _ hsym hpos).2
  have hθ : ∃ z, thetaChar (T.ta b) T.c₁ T.c₂ (T.h b *ᵥ z) ≠ 0 :=
    ⟨(T.h b)⁻¹ *ᵥ w, by rwa [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]⟩
  obtain ⟨t, ht, hval⟩ := exists_gen hT (F.u k (T.Pf (T.co b))) (F.ex k (T.Pf (T.co b)))
    (fun z => thetaChar (T.ta b) T.c₁ T.c₂ (T.h b *ᵥ z)) (fun j z => T.fr j (b, z)) κ hκ hθ
    (fun j z hz => T.fr_ne j b z hb hz) s hs
  exact ⟨⟨F.u k (T.Pf (T.co b)), F.over_σ k _ hP, u, htan, heig, hbas, t, ht⟩, rfl, hu, hval⟩

end GlobalTheory.FrameUnif.ThetaPtEx
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames

theorem _root_.GlobalTheory.T.exists_local_generator_stable_baseChange : Out.SecBaseChangeSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (S : Type) [CommRing S] (x : Sp S ⟶ Xo.X) (p : Sp S), ∃ g : S, g ∉ p.asIdeal ∧ ∃ θ : LB.Sec (PPx (spMap (algebraMap S (Localization.Away g)) ≫ x)), ∀ (T : Type) [CommRing T] (ψ : Localization.Away g →+* T) (x' : Sp T ⟶ Xo.X) (θ' : LB.Sec (PPx x')), x' = spMap ψ ≫ spMap (algebraMap S (Localization.Away g)) ≫ x → SecBC ψ 1 _ x' θ θ' → SecGen x' θ' ∧ SecNZ x' θ' := by
  first | exact @GlobalTheory.Frames.exists_local_generator | exact GlobalTheory.Frames.exists_local_generator | (intros; apply GlobalTheory.Frames.exists_local_generator <;> assumption)
end

section

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped Matrix nonZeroDivisors
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G.Key ReciprocityTheory.ChartRestriction.G.Key.Chi

namespace GlobalTheory

theorem thetaFrame_det_mul_sq_invariant : (∀ (Y : Type) [AddCommGroup Y] [Module.Free ℤ Y] [Module.Finite ℤ Y] (σ : Y ≃ₗ[ℤ] Y) (n M : ℕ), 0 < n → σ ^ n = 1 → 3 ≤ M → (∀ y, ∃ z, σ y = y + M • z) → σ = 1) → Out.SecTwistSt → (∀ (g : ℕ) (ga : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ), ga ∈ Matrix.symplecticGroup (Fin g) ℤ → (∀ i j, (8 : ℤ) ∣ ga (Sum.inl i) (Sum.inr j) ∧ (8 : ℤ) ∣ ga (Sum.inr i) (Sum.inl j)) → (∀ τ ∈ SiegelH (Fin g), ∀ z : Fin g → ℂ, theta (halfVec 0) (halfVec 0) (zAct ga τ z) (spAct ga τ) ^ 2 = ((ZMod.χ₄ ((ga.toBlocks₂₂.det : ℤ) : ZMod 4) : ℤ) : ℂ) * (jAut ga τ).det * eC (expArg ga τ z) * theta (halfVec 0) (halfVec 0) z τ ^ 2)) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (U : FamilyUnif Xo σ ty) (i : Fin U.n) (m : ℕ) (B : Set (Fin m → ℂ)) (P : (Fin m → ℂ) → ((U.Di i).La →+ (Fin g → ℂ))) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] (U.Di i).La) (h τ : (Fin m → ℂ) → Matrix (Fin g) (Fin g) ℂ) (c₁ c₂ : Fin g → ℂ) (fr : Xo.univ.t.PP.L.ι → (Fin m → ℂ) × (Fin g → ℂ) → ℂ), (∀ b ∈ B, IsPeriod (U.Di i) ty (P b)) → (∀ a a', (U.Di i).EF (bas a) (bas a') = -omegaStd a a') → (∀ k, ∃ e, H.w0 ^ 4 • bas (Pi.single (Sum.inl k) 1) = bas (Pi.single (Sum.inl k) 1) + (8 : ℕ) • e) ∧ (∀ k, ∃ e, H.w0 ^ 4 • bas (Pi.single (Sum.inr k) 1) = (8 : ℕ) • e) → (∀ b ∈ B, (∀ k, h b *ᵥ P b (bas (Pi.single (Sum.inl k) 1)) = Pi.single k 1 ∧ h b *ᵥ P b (bas (Pi.single (Sum.inr k) 1)) = τ b *ᵥ Pi.single k 1)) → (∀ k, c₁ k = 0 ∨ c₁ k = 1 / 2) → (∀ k, c₂ k = 0 ∨ c₂ k = 1 / 2) → (∀ j, DifferentiableOn ℂ (fr j) {bz | bz.1 ∈ B ∧ ⊤ ≤ (U.ex i (P bz.1) bz.2).left ⁻¹ᵁ Xo.univ.t.PP.L.U j}) → (∀ j b z, b ∈ B → ⊤ ≤ (U.ex i (P b) z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j → fr j (b, z) ≠ 0) → (∀ j j' b z, b ∈ B → ⊤ ≤ (U.ex i (P b) z).left ⁻¹ᵁ (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U j') → fr j (b, z) = valAt' (U.ex i (P b) z).left (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U j') (Xo.univ.t.PP.L.g j j').val * fr j' (b, z)) → (∀ j b, b ∈ B → ⊤ ≤ (U.ex i (P b) 0).left ⁻¹ᵁ Xo.univ.t.PP.L.U j → fr j (b, 0) = valAt' (U.u i (P b)) ((Xo.univ.t.PP.L.pull (eSec Xo.univ.t.G)).U (fun _ => j)) (Xo.univ.t.PP.rig.s (fun _ => j)).val) → (∀ b ∈ B, ∃ s : (Xo.univ.t.PP.L.pull (pullback.fst Xo.univ.t.G.hom (U.u i (P b)))).Sec, ∀ j z (x : Sp ℂ ⟶ pullback Xo.univ.t.G.hom (U.u i (P b))), x ≫ pullback.fst _ _ = (U.ex i (P b) z).left → x ≫ pullback.snd _ _ = 𝟙 _ → ⊤ ≤ (U.ex i (P b) z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j → valAt' x ((Xo.univ.t.PP.L.pull (pullback.fst Xo.univ.t.G.hom (U.u i (P b)))).U (fun _ => j)) (s.f (fun _ => j)) = thetaChar (τ b) c₁ c₂ (h b *ᵥ z) * fr j (b, z)) → ∀ b ∈ B, ∀ b' ∈ B, ∀ (gam : (U.Di i).La ≃ₗ[𝓞 E] (U.Di i).La) (h₀ : Matrix (Fin g) (Fin g) ℂ), (∀ a b, (U.Di i).EF (gam a) (gam b) = (U.Di i).EF a b) → (∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) (U.Di i).La), ∃ e, gam a = a + l.M • e) → (∀ a, ∃ e, gam a = a + l.A • e) → (∀ a, P b' (gam a) = h₀ *ᵥ P b a) → ∀ j z, ⊤ ≤ (U.ex i (P b) z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j → (h b).det * (thetaChar (τ b) c₁ c₂ (h b *ᵥ z) * fr j (b, z)) ^ 2 = (h b').det * h₀.det * (thetaChar (τ b') c₁ c₂ (h b' *ᵥ (h₀ *ᵥ z)) * fr j (b', h₀ *ᵥ z)) ^ 2 := by
  intro hMink hT hlaw E _ _ _ H D l Xo σ g ty U i m B P bas h τ c₁ c₂ fr hP hbas hw hn h₁ h₂ hd hne hc h0 hs
    b hb b' hb' gam h₀ hiso hhalf hA hPP j z hz
  have riem : ∀ b ∈ B, IsUnit (h b).det ∧ τ b ∈ SiegelH (Fin g) := fun b hb => by
    obtain ⟨h', τ', -, hu, hsy, hpos, huniq⟩ :=
      (RiemannRel.riemann_relations E H (U.Di i) g ty bas hbas).1 (P b) (hP b hb)
    obtain ⟨e1, e2⟩ := huniq _ _ (hn b hb)
    rw [e1, e2]
    exact ⟨hu, hsy, hpos⟩
  obtain ⟨hu, hτ⟩ := riem b hb
  obtain ⟨hu', hτ'⟩ := riem b' hb'
  obtain ⟨hu₀, hpt, hex⟩ := GlobalTheory.T.uniformization_period_lattice_change hMink E H D l Xo σ g ty U i (P b) (P b') gam h₀ (hP b hb)
    (hP b' hb') hiso hhalf hA hPP
  have hθ : ∀ b ∈ B, (fun z => thetaChar (τ b) c₁ c₂ (h b *ᵥ z)) ≠ 0 := fun b hb hz => by
    obtain ⟨hu, hτ⟩ := riem b hb
    obtain ⟨n, rfl⟩ := ThetaRatio.exists_eq_halfVec h₁
    obtain ⟨n', rfl⟩ := ThetaRatio.exists_eq_halfVec h₂
    refine theta_ne_zero hτ (halfVec n) (halfVec n') (funext fun w => ?_)
    have := congrFun hz ((h b)⁻¹ *ᵥ w)
    simp only [ThetaRatio.thetaChar_ofRealVec, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hu,
      Matrix.one_mulVec] at this
    exact this
  obtain ⟨ρ, κ, hρd, hρ0, hρ1, hκ, hrel, hfr⟩ := thetaFrame_ratio hT E H D l Xo σ g ty U i m B P
    (fun b z => thetaChar (τ b) c₁ c₂ (h b *ᵥ z)) fr hP hd hne hc h0 hs b hb b' hb' h₀
    (hθ b hb) (hθ b' hb') hu₀ hpt hex
  have hfull := LevelHalf.trivial_mod_of_trivial_on_half E H (U.Di i) l gam hiso hhalf
  have hiso' : ∀ a b, (U.Di i).EF (gam.symm a) (gam.symm b) = (U.Di i).EF a b := fun a b => by
    rw [← hiso, gam.apply_symm_apply, gam.apply_symm_apply]
  have hfull' : ∀ a, ∃ e, gam.symm a = a + l.M • e := fun a => by
    obtain ⟨e, he⟩ := hfull (gam.symm a)
    rw [gam.apply_symm_apply] at he
    refine ⟨-e, ?_⟩
    rw [smul_neg]
    exact eq_add_neg_of_add_eq he.symm
  let N : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ :=
    Matrix.of fun u v => bas.symm (gam.symm (bas (Pi.single v 1))) u
  obtain ⟨h8, hdet⟩ := AdaptedDet.blocks_det_mod_eight E H (U.Di i) g l.M bas gam.symm N hw
    l.three_le hiso' hfull' (fun _ _ => rfl)
  have hcomp : ∀ a, (h b' * h₀) *ᵥ P b (gam.symm a) = h b' *ᵥ P b' a := fun a => by
    rw [← Matrix.mulVec_mulVec, ← hPP, gam.apply_symm_apply]
  obtain ⟨ga, hga, hgae, hτe, hhe, hde⟩ := PeriodChange.period_change E H (U.Di i) g bas gam.symm N
    (P b) ((P b).comp gam.symm.toLinearMap.toAddMonoidHom) (h b) (h b' * h₀) (τ b) (τ b') hbas hiso'
    (fun _ _ => rfl) (fun _ => rfl) (hn b hb)
    (fun k => ⟨(hcomp _).trans (hn b' hb' k).1, (hcomp _).trans (hn b' hb' k).2⟩) hτ hτ' hu
  have h8ga : ∀ i j, (8 : ℤ) ∣ ga (Sum.inl i) (Sum.inr j) ∧ (8 : ℤ) ∣ ga (Sum.inr i) (Sum.inl j) :=
    fun i j => by
      rw [hgae]
      exact h8 j i
  have hχ : ((ZMod.χ₄ ((ga.toBlocks₂₂.det : ℤ) : ZMod 4) : ℤ) : ℂ) = 1 := by
    have e : ga.toBlocks₂₂.det = N.toBlocks₁₁.det := by
      rw [hgae, Matrix.toBlocks_fromBlocks₂₂, Matrix.det_transpose]
    have e' : ((ga.toBlocks₂₂.det : ℤ) : ZMod 4) = 1 := by
      have h4 : ((4 : ℕ) : ℤ) ∣ N.toBlocks₁₁.det - 1 := Dvd.dvd.trans (by norm_num) hdet
      have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 4).2 h4
      rw [Int.cast_sub, Int.cast_one, sub_eq_zero] at this
      rw [e, this]
    rw [e', map_one, Int.cast_one]
  have hl := hlaw g ga hga h8ga
  rw [hχ] at hl
  have dl : Differentiable ℂ (fun w : Fin g → ℂ => (h b)⁻¹ *ᵥ w) :=
    (LinearMap.toContinuousLinearMap (Matrix.mulVecLin (h b)⁻¹)).differentiable
  have hκ2 := ThetaRatio.ratio_sq_eq_det_jAut g ga hga h8ga hl c₁ c₂ h₁ h₂ (τ b) hτ
    (fun w => ρ ((h b)⁻¹ *ᵥ w)) κ (hρd.comp dl) (fun w => hρ0 _)
    (by simp only [Matrix.mulVec_zero, hρ1]) hκ (fun w => by
      have := hrel ((h b)⁻¹ *ᵥ w)
      simp only [Matrix.mulVec_mulVec, ← Matrix.mul_assoc] at this
      rw [hhe, Matrix.mul_nonsing_inv _ hu, Matrix.one_mulVec, Matrix.mul_assoc,
        Matrix.mul_nonsing_inv _ hu, Matrix.mul_one, hτe] at this
      exact this)
  have e := hrel z
  rw [hfr j z hz, hde, Matrix.det_mul, ← hκ2, ← mul_assoc (thetaChar (τ b') c₁ c₂ _), e]
  ring

end GlobalTheory
end
end
