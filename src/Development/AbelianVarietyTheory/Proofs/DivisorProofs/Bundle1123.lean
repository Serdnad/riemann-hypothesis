module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle013
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle037
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.FramedFlatCoordinates
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle018
public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsFlatSecRankZero
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OmegaFactorization
public import Development.AbelianVarietyTheory.Definitions.Divisors.EntireEqOfHalfPlane
public import Mathlib.NumberTheory.NumberField.CMField
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrderLatticeEqSteinitzFormCm
public import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.LevelCuspCharacters
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1091
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemRiemannRochSpaceIffRegularAtEverywhere
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
public import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DifferentiableAtChart
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1092
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.GlintPrincRelIndexNeZero
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsEqnIffGeneratesAtInv
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1093
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1094
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1099
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle783
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle589
import Development.AbelianVarietyTheory.Definitions.Divisors.DetJacMatCoordsEqTransitionJacobianDet
import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialOfFun
import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle007
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueTorusCompat
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle005
import Development.AbelianVarietyTheory.Definitions.Foundations.NormEulerPolySubOneLe
import Development.AutomorphicArithmetic.IntegralCasts.Bundle001
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle001

@[expose] public section

section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.Lev GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.GeoActCompare
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LatStab

section Core

variable {B : Type} [CommRing B] {n : ℕ}

theorem mulVec_mem_iff (S : Subring B) (y : Matrix (Fin n) (Fin n) B) :
    (∀ v : Fin n → B, (∀ i, v i ∈ S) → ∀ i, y.mulVec v i ∈ S) ↔ ∀ i j, y i j ∈ S := by
  constructor
  · intro h i j
    have := h (Pi.single j 1) (fun k => by
      rcases eq_or_ne k j with rfl | hk
      · simp
      · simp [hk]) i
    simpa using this
  · intro h v hv i
    show ∑ j, y i j * v j ∈ S
    exact S.sum_mem fun j _ => S.mul_mem (h i j) (hv j)

theorem exists_int_iff (S : Subring B) (y : GL (Fin n) B) :
    (∃ u : GL (Fin n) S, u.val.map S.subtype = y.val) ↔
      (∀ i j, y.val i j ∈ S) ∧ ∀ i j, (y⁻¹).val i j ∈ S := by
  constructor
  · rintro ⟨u, hu⟩
    have h1 : Units.map (S.subtype.mapMatrix (m := Fin n)).toMonoidHom u = y := Units.ext hu
    subst h1
    refine ⟨fun i j => (u.val i j).2, fun i j => ?_⟩
    rw [← map_inv]
    exact ((u⁻¹).val i j).2
  · rintro ⟨h1, h2⟩
    have inj : Function.Injective (S.subtype.mapMatrix (m := Fin n)) :=
      Matrix.map_injective S.subtype_injective
    let a : Matrix (Fin n) (Fin n) S := Matrix.of fun i j => ⟨_, h1 i j⟩
    let b : Matrix (Fin n) (Fin n) S := Matrix.of fun i j => ⟨_, h2 i j⟩
    have ha : S.subtype.mapMatrix a = y.val := rfl
    have hb : S.subtype.mapMatrix b = (y⁻¹).val := rfl
    refine ⟨⟨a, b, inj ?_, inj ?_⟩, rfl⟩
    · rw [map_mul, ha, hb, map_one, Units.mul_inv]
    · rw [map_mul, ha, hb, map_one, Units.inv_mul]

theorem image_eq_iff {A : Type} [CommRing A] (e : A →+* B) (he : Function.Bijective e) (S : Subring B)
    (β x : GL (Fin n) B) (k : GL (Fin n) A) (hx : x.val = k.val.map e) (L : Set (Fin n → A))
    (hL : ∀ z, z ∈ L ↔ ∀ i, (β⁻¹).val.mulVec (fun a => e (z a)) i ∈ S) :
    k.val.mulVec '' L = L ↔ ∃ u : GL (Fin n) S, u.val.map S.subtype = (β⁻¹ * x * β).val := by
  have key : ∀ (x : GL (Fin n) B) (k : GL (Fin n) A), x.val = k.val.map e →
      ((∀ z ∈ L, k.val.mulVec z ∈ L) ↔ ∀ i j, (β⁻¹ * x * β).val i j ∈ S) := by
    intro x k hx
    have hm : ∀ z : Fin n → A, (β⁻¹).val.mulVec (fun a => e (k.val.mulVec z a)) =
        (β⁻¹ * x * β).val.mulVec ((β⁻¹).val.mulVec (fun a => e (z a))) := by
      intro z
      have : (fun a => e (k.val.mulVec z a)) = x.val.mulVec (fun a => e (z a)) := by
        funext a
        rw [hx, RingHom.map_mulVec]; rfl
      rw [this, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Units.val_mul, ← Units.val_mul,
        mul_inv_cancel_right]
    rw [← mulVec_mem_iff]
    constructor
    · intro h v hv
      choose z hz using fun a => he.2 (β.val.mulVec v a)
      have hz' : (β⁻¹).val.mulVec (fun a => e (z a)) = v := by
        rw [show (fun a => e (z a)) = β.val.mulVec v from funext hz, Matrix.mulVec_mulVec, Units.inv_mul,
          Matrix.one_mulVec]
      have := (hL _).1 (h z ((hL z).2 (by rw [hz']; exact hv)))
      rwa [hm, hz'] at this
    · intro h z hz
      rw [hL, hm]
      exact h _ ((hL z).1 hz)
  have hx' : (x⁻¹).val = (k⁻¹).val.map e := by
    have h1 : Units.map (e.mapMatrix (m := Fin n)).toMonoidHom k = x := Units.ext hx.symm
    rw [← h1, ← map_inv]; rfl
  have hi : (β⁻¹ * x * β)⁻¹ = β⁻¹ * x⁻¹ * β := by group
  rw [exists_int_iff, hi, ← key x k hx, ← key x⁻¹ k⁻¹ hx']
  constructor
  · intro h
    refine ⟨fun z hz => h ▸ ⟨z, hz, rfl⟩, fun z hz => ?_⟩
    rw [← h] at hz
    obtain ⟨w, hw, rfl⟩ := hz
    rwa [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
  · rintro ⟨h1, h2⟩
    apply Set.Subset.antisymm
    · rintro _ ⟨z, hz, rfl⟩
      exact h1 z hz
    · intro z hz
      exact ⟨_, h2 z hz, by rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]⟩

end Core

theorem mem_St_iff {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    (β x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) :
    x ∈ Formalism.L2.DIV.St β ↔ ∃ u : GL (Fin n) (Formalism.L2.Herm.intAf F E),
      u.val.map (Formalism.L2.Herm.intAf F E).subtype = (β⁻¹ * x * β).val := by
  refine exists_congr fun u => ?_
  show β * Formalism.L2.DIV.intGL F E n u * β⁻¹ = x ↔ (Formalism.L2.DIV.intGL F E n u).val = _
  rw [← Units.ext_iff]
  constructor
  · rintro rfl; group
  · intro h; rw [h]; group

theorem gLat_eq_latHat_iff : ∀ (D : D7) (V : HSp D) (r : ℕ) (hr : V.rank = r) (β : GL (Fin r) (EAf D)), LatticeBasisLifts.IsLatBasis V hr β → ∀ κ : GA D V, gLat V κ = (latHat V : Set (Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E)) ↔ LatticeBasisLifts.finR V hr κ ∈ Formalism.L2.DIV.St β := by
  intro D V r hr β hβ κ
  subst hr
  rw [mem_St_iff]
  exact image_eq_iff (swapAE D) (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E).bijective
    (LatticeBasisLifts.OAf D) β _ (finHom V κ) rfl _ hβ

end GlobalTheory.LatStab
end
end

section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.BdryUnit

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.AllWt

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

def SameVec (Y : Model Xo c (RingHom.id c.F)) {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S)
    (u : Sp (DualNumber S) ⟶ Xo.univ.t.G.left) (v : Sp (DualNumber S) ⟶ Y.t.G.left) : Prop :=
  ∃ w : Sp (DualNumber S) ⟶ Y.oF.t.G.left,
    IsTanAtG Y.oF.t (ptF y) w ∧ w ≫ Y.m0.toSABMap.φ = u ∧ w ≫ Y.m.φ = v

def Matches (Y : Model Xo c (RingHom.id c.F)) (V : (Xo.XF c).Opens) (τ : Psi H) {S : Type} [CommRing S] [Algebra c.F S]
    (y : FrPt Xo c S) (a : GlobalTheory.IndefiniteRowSideFullHecke.FramedFlatCoordinates.Framed Y V τ.1 S (algebraMap c.F S)) : Prop :=
  a.x = ptF y ≫ Y.jQ ∧
    (∀ i : Fin Dw.p, ∃ j : Fin (Dw.mult τ.1), (j : ℕ) = i ∧ SameVec Y y (y.u τ.1 j) (a.v i).left) ∧
    ∀ i : Fin Dw.q, ∃ j : Fin (Dw.mult (conjEmb τ.1)), (j : ℕ) = i ∧ SameVec Y y (y.u (conjEmb τ.1) j) (a.w i).left

def Reads (Y : Model Xo c (RingHom.id c.F)) (V : (Xo.XF c).Opens) (τ : Psi H)
    (sig : GlobalTheory.IndefiniteRowSideFullHecke.FramedFlatCoordinates.Rule Y V τ.1) (f : Rul Xo c) : Prop :=
  ∀ (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S), GlobalTheory.FlatLine.Tested y →
    ∀ a : GlobalTheory.IndefiniteRowSideFullHecke.FramedFlatCoordinates.Framed Y V τ.1 S (algebraMap c.F S), Matches Y V τ y a →
      evR Xo c f y = sig S (algebraMap c.F S) a

end GlobalTheory.BdryUnit
end
end

section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.WeightTwoSum
open scoped ContDiff nonZeroDivisors

theorem _root_.GlobalTheory.T.orderLattice_eq_steinitzForm_cm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (c : Ideal (OF E)) (y : (Af E)ˣ), c ≠ ⊥ → ∀ θ : E, θ ∉ maximalRealSubfield E → ∃ (𝔞 𝔟 : Frac (maximalRealSubfield E)) (a₀ : maximalRealSubfield E), ∀ x : E, x ∈ lattice c y ↔ ∃ a ∈ latM 𝔞, ∃ b ∈ (𝔟 : FractionalIdeal (𝓞 (maximalRealSubfield E))⁰ (maximalRealSubfield E)), x = (a : E) + (b : E) * (θ + (a₀ : E)) := by
  first | exact @GlobalTheory.SteinitzOrder.lattice_eq_steinitz | exact GlobalTheory.SteinitzOrder.lattice_eq_steinitz | (intros; apply GlobalTheory.SteinitzOrder.lattice_eq_steinitz <;> assumption)
end

section

noncomputable section

open Formalism.BasicNotions GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.LevelCuspCharacters

namespace GlobalTheory.GoodIdemFlip

section Local

variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] {r : ℕ}

def invParam (s : SSParam p K r) : SSParam p K r := ⟨s.1, fun c => (s.2 c)⁻¹⟩

theorem cycChar_invParam (s : SSParam p K r) (c : Cyc (invParam s).1) : cycChar (invParam s) c = (cycChar s c)⁻¹ := by
  ext x; rfl

theorem rootChar_invParam (s : SSParam p K r) (x : Σ c : Cyc (invParam s).1, Fin (cycLen (invParam s).1 c)) :
    rootChar (invParam s) x = (rootChar s x)⁻¹ := by
  have h : rootChar (invParam s) x = (cycChar s x.1)⁻¹ ^ (p ^ x.2.val) := by
    rw [← cycChar_invParam s x.1]; rfl
  rw [h, inv_pow]
  rfl

theorem congrMod_inv {A : Type} [CommGroup A] (l : ℕ) (a b : A) : CongrMod l a⁻¹ b⁻¹ ↔ CongrMod l a b := by
  have : a⁻¹ / b⁻¹ = (a / b)⁻¹ := by rw [inv_div_inv, inv_div]
  simp only [CongrMod, this, inv_pow, inv_eq_one]

theorem congrMod_inv_left {A : Type} [CommGroup A] (l : ℕ) (a b : A) : CongrMod l a⁻¹ b ↔ CongrMod l a b⁻¹ := by
  rw [← congrMod_inv, inv_inv]

theorem inv_comp_baseNorm (χ : (ZMod p)ˣ →* Kˣ) (D : ℕ) :
    χ⁻¹.comp (baseNorm p D) = (χ.comp (baseNorm p D))⁻¹ := by
  ext x; rfl

theorem goodAt_flip {ι J : Type} (χ : J → ((ZMod p)ˣ →* Kˣ)) (s s' : ι → SSParam p K r)
    (h : ∀ v, s' v = s v ∨ s' v = invParam (s v)) (hs : GoodAt χ s) : GoodAt χ s' := by
  obtain ⟨h1, h2, ⟨h3, h3'⟩, h4, v5, h5⟩ := hs
  refine ⟨fun v => ?_, fun l hl hl' v => ?_, ⟨fun l hl hl' v => ?_, fun v => ?_⟩, ?_, v5, ?_⟩
  · rcases h v with e | e <;> rw [e]
    · exact h1 v
    · intro x y hxy
      rw [rootChar_invParam, rootChar_invParam] at hxy
      exact h1 v (inv_injective hxy)
  · rcases h v with e | e <;> rw [e]
    · exact h2 l hl hl' v
    · intro x y hxy
      rw [rootChar_invParam, rootChar_invParam, congrMod_inv]
      exact h2 l hl hl' v x y hxy
  · rcases h v with e | e <;> rw [e]
    · exact h3 l hl hl' v
    · intro j c
      have := h3 l hl hl' v j c
      rw [inv_comp_baseNorm] at this
      rw [cycChar_invParam, inv_comp_baseNorm, congrMod_inv, congrMod_inv_left]
      exact this.symm
  · rcases h v with e | e <;> rw [e]
    · exact h3' v
    · intro j x
      have := h3' v j x
      rw [inv_comp_baseNorm] at this
      rw [rootChar_invParam, inv_comp_baseNorm, Ne, Ne, inv_inj, inv_eq_iff_eq_inv]
      exact this.symm
  · rintro ⟨a, ha, ha', hA⟩
    refine h4 ⟨a, ha, ha', fun v => ?_⟩
    have := hA v
    rcases h v with e | e <;> rw [e] at this <;> exact this
  · rcases h v5 with e | e <;> rw [e] <;> exact h5

theorem isConj_inv_inv {G : Type} [Group G] {a b : G} (h : IsConj a b) : IsConj a⁻¹ b⁻¹ := by
  obtain ⟨c, rfl⟩ := isConj_iff.1 h
  exact isConj_iff.2 ⟨c, by group⟩

end Local

section Global

variable {R : Ranks} {H : Host R} {K : Type} [Field K]


open Classical in
def flipAt (S : Set (Sq H)) (x : LevelGroup H) : LevelGroup H := fun v => if v ∈ S then (x v)⁻¹ else x v


open Classical in
def flipParam (S : Set (Sq H)) (s : ∀ v : Sq H, SSParam (H.g v.1) K R.r) : ∀ v : Sq H, SSParam (H.g v.1) K R.r :=
  fun v => if v ∈ S then invParam (s v) else s v

theorem flipAt_flipAt (S : Set (Sq H)) (x : LevelGroup H) : flipAt S (flipAt S x) = x := by
  funext v
  by_cases hv : v ∈ S <;> simp [flipAt, hv]

theorem flipAt_one (S : Set (Sq H)) : flipAt S 1 = 1 := by
  funext v
  by_cases hv : v ∈ S <;> simp [flipAt, hv]

theorem tupleChar_flipParam (S : Set (Sq H)) (s : ∀ v : Sq H, SSParam (H.g v.1) K R.r) :
    tupleChar (flipParam S s) = tupleChar s ∘ flipAt S := by
  funext x
  refine Finset.prod_congr rfl fun v _ => ?_
  by_cases hv : v ∈ S
  · simp only [flipParam, flipAt, if_pos hv]
    exact (GlobalTheory.TypeCharacterConjugateInverse.typeChar_conj_inv _ K _ (s v)).2 (x v)
  · simp only [flipParam, flipAt, if_neg hv]

theorem tupleChar_congr (s : ∀ v : Sq H, SSParam (H.g v.1) K R.r) {x y : LevelGroup H}
    (h : ∀ v, IsConj (x v) (y v)) : tupleChar s x = tupleChar s y :=
  Finset.prod_congr rfl fun v _ => (GlobalTheory.TypeCharacterConjugateInverse.typeChar_conj_inv _ K _ (s v)).1 _ _ (h v)

theorem comp_flipAt_mem (om : ∀ i : Fin 2, (ZMod (H.g i))ˣ →* Kˣ) (S : Set (Sq H)) {τ : LevelGroup H → K}
    (hτ : τ ∈ goodTypes om) : τ ∘ flipAt S ∈ goodTypes om := by
  obtain ⟨s, hs, rfl⟩ := hτ
  refine ⟨flipParam S s, fun i => goodAt_flip _ _ _ (fun w => ?_) (hs i), tupleChar_flipParam S s⟩
  by_cases hv : (⟨i, w⟩ : Sq H) ∈ S
  · exact Or.inr (if_pos hv)
  · exact Or.inl (if_neg hv)

end Global

theorem coeff_goodIdem_flip (R : Ranks) (H : Host R) (om : ∀ i : Fin 2, (ZMod (H.g i))ˣ →* ℂˣ) (S : Set (Sq H))
    (x y : LevelGroup H) (h1 : ∀ v ∈ S, IsConj (x v)⁻¹ (y v)) (h2 : ∀ v ∉ S, IsConj (x v) (y v)) :
    (goodIdem om).coeff y = (goodIdem om).coeff x := by
  simp only [goodIdem, MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply, GlobalTheory.SumWCompare.coeff_centralIdem]
  have inv : ∀ τ : LevelGroup H → ℂ, (τ ∘ flipAt S) ∘ flipAt S = τ := fun τ => by
    funext z; simp [flipAt_flipAt]
  refine Finset.sum_nbij' (fun τ => τ ∘ flipAt S) (fun τ => τ ∘ flipAt S) ?_ ?_ (fun τ _ => inv τ) (fun τ _ => inv τ) ?_
  · intro τ hτ
    exact (Set.Finite.mem_toFinset _).2 (comp_flipAt_mem om S ((Set.Finite.mem_toFinset _).1 hτ))
  · intro τ hτ
    exact (Set.Finite.mem_toFinset _).2 (comp_flipAt_mem om S ((Set.Finite.mem_toFinset _).1 hτ))
  · intro τ hτ
    obtain ⟨s, -, rfl⟩ := (Set.Finite.mem_toFinset _).1 hτ
    have key : tupleChar s y⁻¹ = tupleChar s (flipAt S x⁻¹) := by
      refine tupleChar_congr s fun v => ?_
      by_cases hv : v ∈ S
      · simp only [flipAt, if_pos hv, Pi.inv_apply]
        exact isConj_inv_inv (h1 v hv).symm
      · simp only [flipAt, if_neg hv, Pi.inv_apply]
        exact isConj_inv_inv (h2 v hv).symm
    rw [Function.comp_apply, Function.comp_apply, flipAt_one, key]

end GlobalTheory.GoodIdemFlip
end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar

namespace GlobalTheory.ProjVar

theorem exists_veryAmpleBy_O1 : ∀ Y : Var ℂ, ∃ s : Fin (Y.N + 1) → ((ProjSpace.O1 ℂ Y.N).pull Y.ι).Sec, GlobalTheory.AbLaw.VeryAmpleBy Y.str ((ProjSpace.O1 ℂ Y.N).pull Y.ι) s :=
  fun Y => ⟨_, ProjSpace.veryAmpleBy_secPull_coord Y.ι⟩

end GlobalTheory.ProjVar
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.finrank_sections_pullback_finite_flat_degree_bounds : ∀ (K : Type) [Field K] (X X' : Scheme.{0}) [IsIntegral X] [IsIntegral X'] (f : X ⟶ Spec (CommRingCat.of K)) (φ : X' ⟶ X) [IsFinite φ] [Flat φ] [Surjective φ] (H : LB X) (n : ℕ) (s : Fin (n + 1) → LB.Sec H), H.IsLB → VeryAmpleBy f H s → ∀ d : ℕ, (∀ x : X, φ.finrank x = d) → (∀ t : ℕ, Module.Finite K (SecOnR f (pw H t) ⊤)) → (∀ t : ℕ, Module.Finite K (SecOnR (φ ≫ f) ((pw H t).pull φ) ⊤)) → ∃ a : ℕ, ∀ t : ℕ, d * Module.finrank K (SecOnR (f) (pw H t) ⊤) ≤ Module.finrank K (SecOnR (φ ≫ f) ((pw H (t + a : ℕ)).pull φ) ⊤) ∧ Module.finrank K (SecOnR (φ ≫ f) ((pw H t).pull φ) ⊤) ≤ d * Module.finrank K (SecOnR (f) (pw H (t + a : ℕ)) ⊤) := by
  first | exact @GlobalTheory.finrank_sec_pull_sandwich_flat | exact GlobalTheory.finrank_sec_pull_sandwich_flat | (intros; apply GlobalTheory.finrank_sec_pull_sandwich_flat <;> assumption)
end

section

open NumberField IsDedekindDomain GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun Matrix

namespace GlobalTheory.GLFinPlaces

theorem gl_mem_int_cofinite (E : Type) [Field E] [NumberField E] (a : ℕ) (k : GL (Fin a) (Af E)) :
    {w : HeightOneSpectrum (𝓞 E) | GeneralLinearGroup.map (pLoc E w) k ∉ KGL w (n := a)}.Finite := by
  have hent : ∀ M : Matrix (Fin a) (Fin a) (Af E), ∀ᶠ w in Filter.cofinite,
      ∀ i j, (M i j) w ∈ w.adicCompletionIntegers E := by
    intro M
    rw [Filter.eventually_all]; intro i
    rw [Filter.eventually_all]; intro j
    exact (M i j).2
  have h := (hent (k : Matrix (Fin a) (Fin a) (Af E))).and (hent ((k⁻¹ : GL (Fin a) (Af E)) : Matrix (Fin a) (Fin a) (Af E)))
  rw [Filter.eventually_cofinite] at h
  refine h.subset ?_
  intro w hw
  simp only [Set.mem_setOf_eq] at hw ⊢
  intro hg
  apply hw
  have key : ∀ M : Matrix (Fin a) (Fin a) (Af E), (∀ i j, (M i j) w ∈ w.adicCompletionIntegers E) →
      M.map (pLoc E w) ∈ (RingHom.mapMatrix (m := Fin a) (Ov E w).subtype).range := by
    intro M hM
    exact ⟨Matrix.of fun i j => (⟨(M i j) w, hM i j⟩ : Ov E w), by ext i j; rfl⟩
  refine P.glint_mem_range_of_integral _ _ ?_ ?_
  · exact key _ hg.1
  · rw [← map_inv]
    exact key _ hg.2

end GlobalTheory.GLFinPlaces
end

section

open NumberField IsDedekindDomain GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun Matrix

theorem _root_.GlobalTheory.T.exists_finiteAdelicGL_agree_outside_trivial_on_finset : ∀ (E : Type) [Field E] [NumberField E] (a : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))) (k : GL (Fin a) (Af E)), ∃ k' : GL (Fin a) (Af E), (∀ w ∉ S, GeneralLinearGroup.map (pLoc E w) k' = GeneralLinearGroup.map (pLoc E w) k) ∧ ∀ w ∈ S, GeneralLinearGroup.map (pLoc E w) k' = 1 := by
  first | exact @GlobalTheory.outsideS_elt | exact GlobalTheory.outsideS_elt | (intros; apply GlobalTheory.outsideS_elt <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier


theorem _root_.GlobalTheory.T.exists_section_pow_ample_forall_local_condition : ∀ (W : Scheme.{0}) [IsIntegral W] (H : LB W), IsAmpleLB H → ∀ (P : W → W.functionField → Prop), (∀ y c c', P y c → RegAt y c' → P y (c' * c)) → (∀ y, ∃ (V : W.Opens) (hy : y ∈ V) (d : Γ(W, V)), fnOf V (gen_mem hy) d ≠ 0 ∧ ∀ y' ∈ V, P y' (fnOf V (gen_mem hy) d)) → ∃ n, 1 ≤ n ∧ ∃ t : (lbPow H n).Sec, t ≠ 0 ∧ ∀ (y : W) (i : (lbPow H n).ι) (hi : y ∈ (lbPow H n).U i), P y (fnOf _ (gen_mem hi) (t.f i)) := by
  first | exact @GlobalTheory.exists_sec_forall_local_condition | exact GlobalTheory.exists_sec_forall_local_condition | (intros; apply GlobalTheory.exists_sec_forall_local_condition <;> assumption)
end

section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

theorem _root_.GlobalTheory.T.shintani_lift_kills_cusp_divisible_degree : ∀ (F F' : Type) [Field F] [Field F'] [Algebra F F'] [Finite F'] (s : F' ≃ₐ[F] F'), (Module.finrank F F').Prime → s ≠ 1 → ∀ (ι : AlgebraicClosure F →ₐ[F] AlgebraicClosure F') (θ : AlgebraicClosure F' →* ℂ), (∀ x y : AlgebraicClosure F', x ≠ 0 → y ≠ 0 → θ x = θ y → x = y) → ∀ n k : ℕ, 0 < n → Module.finrank F F' ∣ n → Reg (Nat.card F) n k → Kills (shLift s (cusp (pullθ ι θ) n k)) (J θ (liftL (Nat.card F) (Module.finrank F F') [(n, k)]) n) := by
  first | (exact @GlobalTheory.Shin.shLift_cusp_kills_J) | (exact GlobalTheory.Shin.shLift_cusp_kills_J) | (intros; apply GlobalTheory.Shin.shLift_cusp_kills_J  <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry NumberField GlobalTheory.ChowHt GlobalTheory.Adelic

theorem _root_.GlobalTheory.T.normalizedPointHeightLattice_algebraMap : ∀ (F K : Type) [Field F] [NumberField F] [Field K] [NumberField K] [Algebra F K] (N n : ℕ) (w : Matrix (Fin N) (Fin n) F) (A : (F →+* ℂ) → Matrix (Fin N) (Fin N) ℂ), Submodule.span F (Set.range w.col) = ⊤ → (∀ σ, (A σ).det ≠ 0) → ∀ (K' : Type) [Field K'] [NumberField K'] [Algebra F K'] [Algebra K K'] [IsScalarTower F K K'] (y : Fin N → K), y ≠ 0 → pointHeight w A (fun j => algebraMap K K' (y j)) = pointHeight w A y := by
  first | exact @GlobalTheory.Adelic.HeightExt.pointHeight_algebraMap | exact GlobalTheory.Adelic.HeightExt.pointHeight_algebraMap | (intros; apply GlobalTheory.Adelic.HeightExt.pointHeight_algebraMap <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry NumberField GlobalTheory.ChowHt GlobalTheory.Adelic

theorem _root_.GlobalTheory.T.normalizedPointHeightLattice_smul : ∀ (F K : Type) [Field F] [NumberField F] [Field K] [NumberField K] [Algebra F K] (N n : ℕ) (w : Matrix (Fin N) (Fin n) F) (A : (F →+* ℂ) → Matrix (Fin N) (Fin N) ℂ), Submodule.span F (Set.range w.col) = ⊤ → (∀ σ, (A σ).det ≠ 0) → ∀ (y : Fin N → K) (c : K), y ≠ 0 → c ≠ 0 → pointHeight w A (c • y) = pointHeight w A y := by
  first | exact @GlobalTheory.Adelic.HeightScaling.pointHeight_smul | exact GlobalTheory.Adelic.HeightScaling.pointHeight_smul | (intros; apply GlobalTheory.Adelic.HeightScaling.pointHeight_smul <;> assumption)
end
