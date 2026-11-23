module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle411
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle003
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.FramesDifferByIsometryAndTriangularOfPeriods
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle429
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle066
public import Formalism.LocalToGlobal.IndefiniteReal.FockTheta.RealPlaceImaginaryGeneratorReEqZero
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PureTensorOZeroEqJetP
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle430
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.StarPurelyImaginaryEqNeg
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1992
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
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.LminorSubmatrixCastSucc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.OrthonormalFlagTranslateHolds
import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1199

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HkFam GlobalTheory.Frames GlobalTheory.HeckeEx
open GlobalTheory.IndefiniteRowSideFullHecke.FibrePushforwardExistenceTori (IsLinHom IsLieImg IsThGen IsHeckeIsog)

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HeckeEx

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {P : Ideal (𝓞 E)} {p i : ℕ}

section Map

variable (Z : Corr Xo P p i) {T : Type} [CommRing T] (h : Sp T ⟶ Z.Hk)

def hkLift {x : Sp T ⟶ Xo.X} (hx : x = h ≫ Z.π₁) : Gx x ⟶ Z.o₁.t.G.left :=
  Z.m₁.cart.1.lift (snd (Over.mk x) Xo.univ.t.G).left ((fst (Over.mk x) Xo.univ.t.G).left ≫ h)
    (by rw [GlobalTheory.HeckeFrCompare.snd_hom, Category.assoc, ← hx])

def hkLift₂ {x' : Sp T ⟶ Xo.X} (hx' : x' = h ≫ Z.π₂) : Gx x' ⟶ Z.o₂.t.G.left :=
  Z.m₂.cart.1.lift (snd (Over.mk x') Xo.univ.t.G).left ((fst (Over.mk x') Xo.univ.t.G).left ≫ h)
    (by rw [GlobalTheory.HeckeFrCompare.snd_hom, Category.assoc, ← hx'])

variable {h} {x x' : Sp T ⟶ Xo.X} (hx : x = h ≫ Z.π₁) (hx' : x' = h ≫ Z.π₂)

@[reassoc] theorem hkLift_φ : hkLift Z h hx ≫ Z.m₁.cm.F = (snd (Over.mk x) Xo.univ.t.G).left :=
  Z.m₁.cart.1.lift_fst _ _ _

@[reassoc] theorem hkLift_hom : hkLift Z h hx ≫ Z.o₁.t.G.hom = (fst (Over.mk x) Xo.univ.t.G).left ≫ h :=
  Z.m₁.cart.1.lift_snd _ _ _

def hkMap : Gx x ⟶ Gx x' :=
  pullback.lift (f := (Over.mk x').hom) (g := Xo.univ.t.G.hom) (fst (Over.mk x) Xo.univ.t.G).left
    (hkLift Z h hx ≫ Z.ψ.left ≫ Z.m₂.cm.F) (by
      simp only [Category.assoc]
      rw [Z.m₂.cart.1.w, Over.w_assoc Z.ψ, hkLift_hom_assoc, ← hx']; rfl)

@[reassoc] theorem hkMap_fst :
    hkMap Z hx hx' ≫ (fst (Over.mk x') Xo.univ.t.G).left = (fst (Over.mk x) Xo.univ.t.G).left :=
  pullback.lift_fst _ _ _

@[reassoc] theorem hkMap_snd :
    hkMap Z hx hx' ≫ (snd (Over.mk x') Xo.univ.t.G).left = hkLift Z h hx ≫ Z.ψ.left ≫ Z.m₂.cm.F :=
  pullback.lift_snd _ _ _

end Map

section Square

variable (Z : Corr Xo P p i) {T : Type} [CommRing T] {h : Sp T ⟶ Z.Hk} {x x' : Sp T ⟶ Xo.X}

theorem hkLift_isPullback (hx : x = h ≫ Z.π₁) :
    IsPullback (hkLift Z h hx) (fst (Over.mk x) Xo.univ.t.G).left Z.o₁.t.G.hom h := by
  refine IsPullback.of_right (h₁₂ := Z.m₁.cm.F) (v₁₃ := Xo.univ.t.G.hom) (h₂₂ := Z.π₁) ?_ (hkLift_hom Z hx)
    Z.m₁.cart.1
  rw [hkLift_φ, ← hx]
  exact (IsPullback.of_hasPullback (Over.mk x).hom Xo.univ.t.G.hom).flip

theorem hkLift₂_isPullback (hx' : x' = h ≫ Z.π₂) :
    IsPullback (hkLift₂ Z h hx') (fst (Over.mk x') Xo.univ.t.G).left Z.o₂.t.G.hom h := by
  have hφ : hkLift₂ Z h hx' ≫ Z.m₂.cm.F = (snd (Over.mk x') Xo.univ.t.G).left :=
    Z.m₂.cart.1.lift_fst _ _ _
  have hhom : hkLift₂ Z h hx' ≫ Z.o₂.t.G.hom = (fst (Over.mk x') Xo.univ.t.G).left ≫ h :=
    Z.m₂.cart.1.lift_snd _ _ _
  refine IsPullback.of_right (h₁₂ := Z.m₂.cm.F) (v₁₃ := Xo.univ.t.G.hom) (h₂₂ := Z.π₂) ?_ hhom
    Z.m₂.cart.1
  rw [hφ, ← hx']
  exact (IsPullback.of_hasPullback (Over.mk x').hom Xo.univ.t.G.hom).flip

theorem hkMap_isPullback (hx : x = h ≫ Z.π₁) (hx' : x' = h ≫ Z.π₂) :
    IsPullback (hkLift Z h hx) (hkMap Z hx hx') Z.ψ.left (hkLift₂ Z h hx') := by
  have hφ : hkLift₂ Z h hx' ≫ Z.m₂.cm.F = (snd (Over.mk x') Xo.univ.t.G).left :=
    Z.m₂.cart.1.lift_fst _ _ _
  have hhom : hkLift₂ Z h hx' ≫ Z.o₂.t.G.hom = (fst (Over.mk x') Xo.univ.t.G).left ≫ h :=
    Z.m₂.cart.1.lift_snd _ _ _
  have heq : hkMap Z hx hx' ≫ hkLift₂ Z h hx' = hkLift Z h hx ≫ Z.ψ.left :=
    Z.m₂.cart.1.hom_ext (by rw [Category.assoc, hφ, hkMap_snd, Category.assoc])
      (by rw [Category.assoc, hhom, hkMap_fst_assoc, Category.assoc, Over.w Z.ψ, hkLift_hom])
  refine IsPullback.of_bot ?_ heq.symm (hkLift₂_isPullback Z hx')
  rw [hkMap_fst, Over.w Z.ψ]
  exact hkLift_isPullback Z hx

theorem hkMap_etale (hx : x = h ≫ Z.π₁) (hx' : x' = h ≫ Z.π₂) : Etale (hkMap Z hx hx') :=
  MorphismProperty.of_isPullback (P := @Etale) (hkMap_isPullback Z hx hx') Z.isog.1.2.2.1

theorem hkMap_surjective (hx : x = h ≫ Z.π₁) (hx' : x' = h ≫ Z.π₂) : Surjective (hkMap Z hx hx') :=
  MorphismProperty.of_isPullback (P := @Surjective) (hkMap_isPullback Z hx hx') Z.isog.1.2.2.2.1

end Square

section Fibre

variable (Z : Corr Xo P p i) {T : Type} [CommRing T] {h : Sp T ⟶ Z.Hk} {x x' : Sp T ⟶ Xo.X}

@[reassoc] theorem isCan_hkLift {Ω : Type} [CommRing Ω] {χ : T →+* Ω} {x₁ : Sp Ω ⟶ Xo.X} {pm : Gx x₁ ⟶ Gx x}
    (hx : x = h ≫ Z.π₁) (hp : IsCan χ pm) (h₁ : x₁ = (spMap χ ≫ h) ≫ Z.π₁) :
    pm ≫ hkLift Z h hx = hkLift Z (spMap χ ≫ h) h₁ :=
  Z.m₁.cart.1.hom_ext (by rw [Category.assoc, hkLift_φ, hkLift_φ, hp.2.1])
    (by rw [Category.assoc, hkLift_hom, hkLift_hom, reassoc_of% hp.2.2])

theorem isFib_hkMap {Ω : Type} [CommRing Ω] (χ : T →+* Ω) (hx : x = h ≫ Z.π₁) (hx' : x' = h ≫ Z.π₂)
    {x₁ x₁' : Sp Ω ⟶ Xo.X} {Ψ₁ : Gx x₁ ⟶ Gx x₁'} (hΨ : IsFib χ (hkMap Z hx hx') Ψ₁) :
    ∃ (h₁ : x₁ = (spMap χ ≫ h) ≫ Z.π₁) (h₂ : x₁' = (spMap χ ≫ h) ≫ Z.π₂), Ψ₁ = hkMap Z h₁ h₂ := by
  obtain ⟨pm, pm', hp, hp', e, f⟩ := hΨ
  have h₁ : x₁ = (spMap χ ≫ h) ≫ Z.π₁ := by rw [hp.1, hx, Category.assoc]
  have h₂ : x₁' = (spMap χ ≫ h) ≫ Z.π₂ := by rw [hp'.1, hx', Category.assoc]
  refine ⟨h₁, h₂, GlobalTheory.HeckeFrCompare.gx_ext (f.trans (hkMap_fst Z h₁ h₂).symm) ?_⟩
  rw [hkMap_snd Z h₁ h₂, ← isCan_hkLift_assoc Z hx hp h₁, ← hkMap_snd Z hx hx', ← reassoc_of% e, hp'.2.1]

end Fibre

end GlobalTheory.HeckeEx
end
end

section

open NumberField AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.HeckeEx
open GlobalTheory.Dict (castFr)
open GlobalTheory.FrameNorm (IsUnitFr)
open scoped Matrix ComplexConjugate

noncomputable section

namespace GlobalTheory.PeriodBorelQ

open GlobalTheory.FramePeriod GlobalTheory.PeriodBorel

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem natPer_move_q {X X' : Data E r} {N : ℕ} {a : GL (Fin r) E} (h : QMatch X X' N a) (τ : E →+* ℂ) (q : ℕ)
    (M : Matrix (Fin r) (Fin r) ℂ) (v : Fin r → E) (n : ℕ) :
    natPer τ X'.Gm q ((a : Matrix (Fin r) (Fin r) E).map τ * M)
      (Data.emb τ ((a : Matrix (Fin r) (Fin r) E) *ᵥ v)) n = natPer τ X.Gm q M (Data.emb τ v) n := by
  have he : Data.emb τ ((a : Matrix (Fin r) (Fin r) E) *ᵥ v) =
      (a : Matrix (Fin r) (Fin r) E).map τ *ᵥ Data.emb τ v := by
    funext k; simp [Data.emb, Matrix.mulVec, dotProduct, map_sum, map_mul]
  have hu : IsUnit ((a : Matrix (Fin r) (Fin r) E).map τ).det := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact ((Matrix.isUnit_iff_isUnit_det _).1 a.isUnit).map τ
  unfold natPer
  split_ifs with hn
  · rw [he, locPer_apply, locPer_apply]
    split_ifs
    · exact h.hermC_eq τ (col M ⟨n, hn⟩) _
    · rw [Matrix.mul_inv_rev, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul_cancel_right _ _ hu]
  · rfl

theorem natPer_natCast_smul (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (q : ℕ) (M : Matrix (Fin r) (Fin r) ℂ)
    (N : ℕ) (v : Fin r → E) (n : ℕ) :
    natPer τ G q M (Data.emb τ ((N : E) • v)) n = (N : ℂ) * natPer τ G q M (Data.emb τ v) n := by
  have he : Data.emb τ ((N : E) • v) = (N : ℂ) • Data.emb τ v := by
    funext k; simp [Data.emb]
  unfold natPer
  split_ifs with hn
  · rw [he, locPer_apply, locPer_apply]
    split_ifs
    · rw [FD.hermC_smul_right, Complex.conj_natCast]
    · rw [Matrix.mulVec_smul]; rfl
  · simp

theorem borel_of_periods_q : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X X' : Data E r) (N : ℕ) (a : GL (Fin r) E) (h : QMatch X X' N a), 0 < N → ∀ (m : (E →+* ℂ) → ℕ), (∀ τ ∈ X.Ψ, m τ = r - X.p0) → (∀ τ ∉ X.Ψ, m τ = X.p0) → ∀ x ∈ X.dom, ∀ x' ∈ X'.dom, ∀ (A : (E →+* ℂ) → ℕ → ℕ → ℂ), (∀ τ i j, j < i → A τ i j = 0) → (∀ τ, ∀ i < m τ, ∀ v ∈ X.Λ, Formalism.L2.PjFree.perFr X' x' ((a : Matrix (Fin r) (Fin r) E) *ᵥ v) τ i = ∑ j ∈ Finset.range (m τ), A τ i j * Formalism.L2.PjFree.perFr X x v τ j) → ∃ b ∈ Bor X'.Ψ r, x' = rmul (lact a (castFr h.psi x)) b ∧ (IsUnitFr X x → IsUnitFr X' x' → (∀ τ i, ‖b τ i i‖ = 1) ∧ ∀ τ, ∀ i < m τ, ‖A τ i i‖ = 1) := by
  intro E _ _ _ r X X' N a h hN0 m hm1 hm2 x hx x' hx' A hA hper
  have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hN0.ne'
  have hz := h.mem_dom hx
  set z := lact a (castFr h.psi x) with hzd
  have hlat : ∀ w ∈ X'.Λ, ∃ v ∈ X.Λ, (a : Matrix (Fin r) (Fin r) E) *ᵥ v = (N : E) • w := by
    intro w hw
    refine ⟨_, h.lat' w hw, ?_⟩
    rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
  have hloc := fun τ : X'.Ψ => loc_borel X' τ.1 (mat z τ) (mat x' τ) (hz τ).1 (hx' τ).1 (A τ.1) (A (conjEmb τ.1))
    (hA _) (hA _)
    (fun i hi w hw => by
      obtain ⟨v, hv, hav⟩ := hlat w hw
      have hm := hm1 τ.1 (h.mem τ)
      rw [h.p0] at hm
      refine mul_left_cancel₀ hN ?_
      rw [← natPer_natCast_smul, ← hav, ← perFr_mem X' x' _ τ.1 τ.2, hper τ.1 i (hm ▸ hi) v hv, hm,
        Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [perFr_mem X x v τ.1 (h.mem τ), ← natPer_move_q h, h.p0, hav, natPer_natCast_smul, mul_left_comm]
      rfl)
    (fun i hi w hw => by
      obtain ⟨v, hv, hav⟩ := hlat w hw
      have hm := hm2 _ (conjEmb_not_mem X (h.mem τ))
      rw [h.p0] at hm
      refine mul_left_cancel₀ hN ?_
      rw [← natPer_natCast_smul, ← hav, ← perFr_conj X' x' _ τ.1 τ.2 i hi, hper _ i (hm ▸ hi) v hv, hm,
        Finset.mul_sum]
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [perFr_conj X x v τ.1 (h.mem τ) j (h.p0 ▸ Finset.mem_range.1 hj), ← natPer_move_q h, h.p0, hav,
        natPer_natCast_smul, mul_left_comm]
      rfl)
  let b : Frame X'.Ψ r := fun τ => ((mat z τ)⁻¹ * mat x' τ : Matrix (Fin r) (Fin r) ℂ)
  have hb : b ∈ Bor X'.Ψ r := fun τ => by
    refine ⟨?_, (hloc τ).1⟩
    show ((mat z τ)⁻¹ * mat x' τ).det ≠ 0
    rw [Matrix.det_mul, Matrix.det_nonsing_inv, Ring.inverse_eq_inv']
    exact mul_ne_zero (inv_ne_zero (hz τ).1) (hx' τ).1
  have hxb : x' = rmul z b := by
    funext τ
    exact (Matrix.mul_nonsing_inv_cancel_left (mat z τ) (mat x' τ) (isUnit_iff_ne_zero.2 (hz τ).1)).symm
  refine ⟨b, hb, hxb, fun hu hu' => ?_⟩
  have hbd : ∀ τ i, ‖b τ i i‖ = 1 := by
    intro τ i
    have e := FrameDegreeData.ratio_rmul X' z hz hb τ i
    rw [← hxb, norm_div, norm_div, hu', hu', hzd, h.dmin_eq, h.dmin_eq, hu, hu, div_one, _root_.mul_one] at e
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 e.symm
  refine ⟨hbd, fun τ i hi => ?_⟩
  by_cases hτ : τ ∈ X.Ψ
  · rw [hm1 τ hτ, h.p0] at hi
    exact ((hloc ⟨τ, h.psi ▸ hτ⟩).2 (hbd _)).1 i hi
  · rw [hm2 τ hτ, h.p0] at hi
    have := ((hloc ⟨conjEmb τ, h.psi ▸ conjEmb_mem X hτ⟩).2 (hbd _)).2 i hi
    rwa [GlobalTheory.PeriodBorel.conjEmb_conjEmb] at this

end GlobalTheory.PeriodBorelQ
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FockTransl
open Formalism.L2.Ker (VCx DVar derivAt0)

noncomputable section

namespace GlobalTheory.FockOmega

variable {D : D7}

open GlobalTheory.FockTransport

theorem jm_mul_self {n : ℕ} (ε : Fin n → Bool) : Formalism.REAL.Jm ε * Formalism.REAL.Jm ε = 1 := by
  rw [Formalism.REAL.Jm, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext a
  cases ε a <;> simp

theorem jm_eq {n : ℕ} (ε : Fin n → Bool) : Formalism.REAL.Jm ε = Matrix.diagonal fun a => ((sg (ε a) : ℝ) : ℂ) := by
  rw [Formalism.REAL.Jm]
  congr 1
  funext a
  cases ε a <;> simp [sg]

theorem gramAt_inv {V : HSp D} (A : GlobalTheory.ChainFr.Fr V) (τ : D.what₂.Tau) :
    (gramAt D V τ)⁻¹ = (A.fr τ)⁻¹ * Formalism.REAL.Jm (A.ε τ) * ((A.fr τ)⁻¹)ᴴ := by
  have hP := det_fr_unit A τ
  rw [← A.fr_gram τ]
  apply Matrix.inv_eq_left_inv
  have h1 : ((A.fr τ)⁻¹)ᴴ * (A.fr τ)ᴴ = 1 := by
    rw [← Matrix.conjTranspose_mul, Matrix.mul_nonsing_inv _ hP, Matrix.conjTranspose_one]
  calc (A.fr τ)⁻¹ * Formalism.REAL.Jm (A.ε τ) * ((A.fr τ)⁻¹)ᴴ * ((A.fr τ)ᴴ * Formalism.REAL.Jm (A.ε τ) * A.fr τ)
      = (A.fr τ)⁻¹ * Formalism.REAL.Jm (A.ε τ) * (((A.fr τ)⁻¹)ᴴ * (A.fr τ)ᴴ) * Formalism.REAL.Jm (A.ε τ) * A.fr τ := by
        simp only [Matrix.mul_assoc]
    _ = (A.fr τ)⁻¹ * (Formalism.REAL.Jm (A.ε τ) * Formalism.REAL.Jm (A.ε τ)) * A.fr τ := by
        rw [h1]; simp only [Matrix.mul_one, Matrix.mul_assoc]
    _ = 1 := by rw [jm_mul_self, Matrix.mul_one, Matrix.nonsing_inv_mul _ hP]

theorem hAt_frame {S T : HSp D} (A : GlobalTheory.ChainFr.Fr S) (B : GlobalTheory.ChainFr.Fr T) (τ : D.what₂.Tau)
    (X Y : Matrix (Fin T.rank) (Fin S.rank) ℂ) :
    GlobalTheory.VacUnique.hAt S T τ ((B.fr τ)⁻¹ * X * A.fr τ) ((B.fr τ)⁻¹ * Y * A.fr τ) =
      (Formalism.REAL.Jm (A.ε τ) * (Yᴴ * (Formalism.REAL.Jm (B.ε τ) * X))).trace := by
  have hA := det_fr_unit A τ
  have hB := det_fr_unit B τ
  have cA : ∀ M : Matrix (Fin S.rank) (Fin S.rank) ℂ, ((A.fr τ)⁻¹)ᴴ * ((A.fr τ)ᴴ * M) = M := fun M => by
    rw [← Matrix.mul_assoc, ← Matrix.conjTranspose_mul, Matrix.mul_nonsing_inv _ hA, Matrix.conjTranspose_one,
      Matrix.one_mul]
  have cB : ∀ M : Matrix (Fin T.rank) (Fin S.rank) ℂ, ((B.fr τ)⁻¹)ᴴ * ((B.fr τ)ᴴ * M) = M := fun M => by
    rw [← Matrix.mul_assoc, ← Matrix.conjTranspose_mul, Matrix.mul_nonsing_inv _ hB, Matrix.conjTranspose_one,
      Matrix.one_mul]
  rw [GlobalTheory.VacUnique.hAt, gramAt_inv A τ, ← B.fr_gram τ]
  simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc, cA, cB, Matrix.mul_nonsing_inv_cancel_left _ _ hB]
  rw [Matrix.trace_mul_comm, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc,
    Matrix.mul_nonsing_inv_cancel_right _ _ hA]

theorem trace_jm {m n : ℕ} (a : Fin n → Bool) (b : Fin m → Bool) (X Y : Matrix (Fin m) (Fin n) ℂ) :
    (Formalism.REAL.Jm a * (Yᴴ * (Formalism.REAL.Jm b * X))).trace =
      ∑ i, ∑ j, ((sg (a j) : ℝ) : ℂ) * (conj (Y i j) * (((sg (b i) : ℝ) : ℂ) * X i j)) := by
  rw [Finset.sum_comm]
  simp only [jm_eq, Matrix.trace, Matrix.diag, Matrix.diagonal_mul]
  simp only [Matrix.mul_apply, Matrix.diagonal_apply, ite_mul, zero_mul, mul_ite, mul_zero, Finset.sum_ite_eq,
    Finset.mem_univ, if_true, Finset.mul_sum, Matrix.conjTranspose_apply, RCLike.star_def]

theorem term_re (b a : Bool) (ξ z y : ℂ) (hξ : ξ.re = 0) :
    2 * (ξ * (((sg a : ℝ) : ℂ) * (conj (cf b a y) * (((sg b : ℝ) : ℂ) * cf b a z)))).re =
      -(2 * (ξ.im * (z * conj y).im)) := by
  cases a <;> cases b <;> simp [cf, sg, Complex.mul_re, Complex.mul_im, hξ] <;> ring_nf <;> simp

theorem omO_fockMat (D : D7) (S T : HSp D) (A : GlobalTheory.ChainFr.Fr S) (B : GlobalTheory.ChainFr.Fr T)
    (Z Y : VCx D.what₂.Tau S.rank T.rank) :
    GlobalTheory.VacUnique.omO S T (fun τ => fockMat A B τ (Z τ) : GlobalTheory.FockCompare.RW T S)
      (fun τ => fockMat A B τ (Y τ) : GlobalTheory.FockCompare.RW T S) =
      -(2 * ∑ τ, ‖tauE D τ D.host.xi0‖ * ∑ i, ∑ j, (Z τ i j * conj (Y τ i j)).im) := by
  refine (GlobalTheory.VacUnique.omO_apply S T _ _).trans ?_
  rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun τ _ => ?_
  show GlobalTheory.VacUnique.omAt S T τ (fockMat A B τ (Z τ)) (fockMat A B τ (Y τ)) = _
  rw [GlobalTheory.VacUnique.omAt, fockMat_eq, fockMat_eq, hAt_frame, trace_jm, Formalism.IndefR.Fock.CCR.norm_embedding_hostFormConstant_eq]
  simp only [Finset.mul_sum, Complex.re_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [Matrix.of_apply]
  exact term_re _ _ _ _ _ (Formalism.IndefR.Fock.CCR.realPlace_imaginaryGenerator_re_eq_zero D τ)

end GlobalTheory.FockOmega
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FockTransl
open Formalism.L2.Ker (VCx DVar derivAt0)

noncomputable section

namespace GlobalTheory.FockTransl.Jet

open Complex GlobalTheory.FockCompare GlobalTheory.OrientedHeis

variable {D : D7}

theorem sum_re_im_add_smul {m n a b : ℕ} (U V : Fin a → Fin b → Matrix (Fin m) (Fin n) ℂ) (z e : Fin a → Fin b → ℂ)
    (t : ℝ) :
    ∑ i, ∑ j, ((((z i j + t • e i j).re : ℝ) : ℂ) • U i j + (((z i j + t • e i j).im : ℝ) : ℂ) • V i j) =
      ∑ i, ∑ j, ((((z i j).re : ℝ) : ℂ) • U i j + (((z i j).im : ℝ) : ℂ) • V i j) +
        t • ∑ i, ∑ j, ((((e i j).re : ℝ) : ℂ) • U i j + (((e i j).im : ℝ) : ℂ) • V i j) := by
  rw [Finset.smul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.smul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Complex.add_re, Complex.add_im, Complex.real_smul, Complex.re_ofReal_mul, Complex.im_ofReal_mul,
    Complex.ofReal_add, Complex.ofReal_mul, add_smul, smul_add, mul_smul, Complex.coe_smul]
  abel

theorem fmR_add_smul {S T : HSp D} (A : GlobalTheory.ChainFr.Fr S) (B : GlobalTheory.ChainFr.Fr T) (z e : VCx D.what₂.Tau S.rank T.rank)
    (t : ℝ) : fmR A B (z + t • e) = fmR A B z + t • fmR A B e := by
  funext τ
  exact sum_re_im_add_smul _ _ (z τ) (e τ) t

theorem heis_dRho_fock : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (σ : (D.what₂.Tau → ℂ) →+ AE D), IsStdChar D ψ (-1) → GlobalTheory.FockCompare.Chart θ σ → ∀ (S T : HSp D) (A : GlobalTheory.ChainFr.Fr S) (B : GlobalTheory.ChainFr.Fr T) (h : WO S T → ℂ) (x : WO S T) (z e : VCx D.what₂.Tau S.rank T.rank) (τ : D.what₂.Tau) (v : Matrix (Fin T.rank) (Fin S.rank) ℂ), GlobalTheory.FockTransl.Jet.fmR A B e τ = v → (∀ τ', τ' ≠ τ → GlobalTheory.FockTransl.Jet.fmR A B e τ' = 0) → heisO ψ S T (fockPt σ A B z) (Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ v h) x = deriv (fun t : ℝ => Complex.exp (-((Real.pi : ℂ) * Complex.I) * ((t * GlobalTheory.FockTransl.Jet.omF A B z e : ℝ) : ℂ)) * heisO ψ S T (fockPt σ A B (z + t • e)) h x) 0 := by
  intro D ψ θ σ hψ hC S T A B h x z e τ v hv h0
  have hux : GlobalTheory.AdForm.JetRead.ux τ v = fmR A B e := by
    funext τ' i j
    unfold GlobalTheory.AdForm.JetRead.ux
    split_ifs with hτ
    · subst hτ; rw [← hv]
    · rw [h0 τ' hτ]; rfl
  have hline : ∀ t : ℝ, (lineAt θ τ v t : WO S T) = iotaW σ T S (t • fmR A B e) := fun t => by
    rw [GlobalTheory.AdForm.JetRead.lineAt_eq hC, hux]
  have hfun : (fun t : ℝ => ψ (symplOH S T x (fockPt σ A B z)) *
      heisO ψ S T (lineAt θ τ v t) h (x + fockPt σ A B z)) = fun t : ℝ =>
      Complex.exp (-((Real.pi : ℂ) * Complex.I) * ((t * omF A B z e : ℝ) : ℂ)) *
        heisO ψ S T (fockPt σ A B (z + t • e)) h x := by
    funext t
    have e1 : ψ (symplOH S T x (fockPt σ A B z)) * heisO ψ S T (lineAt θ τ v t) h (x + fockPt σ A B z) =
        heisO ψ S T (fockPt σ A B z) (heisO ψ S T (lineAt θ τ v t) h) x := rfl
    have e2 : fockPt σ A B z = iotaW σ T S (fmR A B z) := rfl
    have e3 : fockPt σ A B (z + t • e) = iotaW σ T S (fmR A B z) + iotaW σ T S (t • fmR A B e) := by
      rw [← AddMonoidHom.map_add (f := _), ← fmR_add_smul]; rfl
    rw [e1, GlobalTheory.OrientedHeis.heisO_heisO, Pi.smul_apply, smul_eq_mul, hline, e3, e2,
      GlobalTheory.OrientedHeis.psi_symplOH hC hψ, hC.pi_iota, LinearMap.map_smul, smul_eq_mul]
    rfl
  show ψ (symplOH S T x (fockPt σ A B z)) *
      deriv (fun t : ℝ => heisO ψ S T (lineAt θ τ v t) h (x + fockPt σ A B z)) 0 = _
  rw [← deriv_const_mul_field, hfun]

end GlobalTheory.FockTransl.Jet

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.VacAny
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU GlobalTheory.WeilM
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA IsDatumB skewGram mulG colV adjV₁)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple Acts SInf At latAtV realAd evI)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.FlipMatch

noncomputable section

namespace GlobalTheory.SmallDat.VacFix

theorem hTens_mixHalfS {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {i j : ℕ} (e : Num G i j)
    (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j) (hWW : Γ.W.J = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.skewGram (spV G i j) (spV₁ G i j) e) (ε : AE D)
    (hε : ε * cA D ε = 0) (γ : GlobalTheory.SmallDat.PtS G i j) (hγ : γ ∈ mixHalfS e ε) :
    hTens (R := AF D.host.F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Γ.V'.J)
      (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Γ.W.J) γ γ = 0 := by
  refine GlobalTheory.BigDat.VacFix.hTens_eq_zero (R := AF D.host.F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) GlobalTheory.DualPairCheck.cA_cA e _ _
    (fun a b => ?_) (fun a b => ?_) ε hε γ (fun a b => ?_) (fun a b => ?_)
  · exact (congrArg (incA D) ((congrFun (congrFun hWW _) _).trans (GlobalTheory.BigDat.VacFix.skewGram_inl_inr _ _ e a b))).trans (map_zero _)
  · exact (congrArg (incA D) ((congrFun (congrFun hWW _) _).trans (GlobalTheory.BigDat.VacFix.skewGram_inr_inl _ _ e a b))).trans (map_zero _)
  · exact GlobalTheory.BigDat.VacFix.isHalf_of_mulG (spW₁ G i j) ε (colV e γ)ᵀ hγ.1 b a
  · refine GlobalTheory.BigDat.VacFix.isHalf_of_mulG (spV₁ G i j) ε ((γ.submatrix id fun k => e (.inr k)).map (cA D)) (fun a b => ?_) a b
    exact neg_injective ((mul_neg _ _).symm.trans (hγ.2 a b))

theorem vac_fixed : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (M : Vol G) (t : T) (i j : ℕ) (e : Num G i j) (Bs : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j) (X : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E)
    (om : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W) (om' : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W), IsTripleOf W M t i j e Bs Γ X → IsTriple Bs Γ X om om' →
    ∀ v : Pl D.host.F, (∀ u ∈ GlobalTheory.SmallDat.latPtS t e v, u ∈ latAtV Γ.V' Γ.W v) →
      ∀ γ ∈ GlobalTheory.SmallDat.genPtS t e v, Acts (evFin D.host.F v) (Γ.M'.co.rho W.ψ γ) (Γ.M'.vac v) (Γ.M'.vac v) := by
  intro D T L sc G W M t i j e Bs Γ X om om' h hT v hL γ hγ
  obtain ⟨-, -, θ, -, hθ⟩ := hT.geo.hM'.vac v
  have h1 := hθ γ (hL γ (GlobalTheory.SmallDat.genPtS_subset t e v hγ))
  have h2 : Bs.ψ (⅟(2 : AF D.host.F) * symp (R := AF D.host.F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig)
      (inclR (F := D.host.F) (AF D.host.F) (θ : D.host.E)) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Γ.V'.J)
      (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Γ.W.J) γ γ) = 1 := by
    rcases hγ with ⟨γ', hγ', rfl⟩ | ⟨-, ε, hε, hγ⟩
    · exact GlobalTheory.BigDat.VacFix.psi_double _ Bs Γ.V' Γ.W _ _ _ _ hT.base hT.geo.hV' hT.geo.hW v θ γ' (hL γ' hγ')
    · unfold symp
      rw [hTens_mixHalfS e Γ h.JWW ε hε.2.1 γ hγ, mul_zero, map_zero, mul_zero, AddChar.map_zero_eq_one]
  rw [h2, one_smul, h.ψ] at h1
  exact h1

end GlobalTheory.SmallDat.VacFix

end
end
