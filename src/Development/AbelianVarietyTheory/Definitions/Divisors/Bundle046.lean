module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle016
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle003
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle012
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle017
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle004
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TopSelfEqLengthOfSmooth
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle016
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle045
public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.Bundle001
public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.GrowthConstantBoundGcR
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1519
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
import Mathlib.RingTheory.PiTensorProduct
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
import Development.AbelianVarietyTheory.Definitions.ThetaValues.SWEqSOf
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory.ChowHt GlobalTheory.TangentOrigin
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalPowers

namespace GlobalTheory.HSCore

structure Quoted : Prop where
  kv : GlobalTheory.Published.KawamataViehweg
  l2 : GlobalTheory.Published.L2ExtensionLogCanonical
  gaga : GlobalTheory.Published.SerreHolomorphicSections
  nef : GlobalTheory.Published.NefNumerics
  chow : GlobalTheory.Published.ChowFormExists
  chowInt : GlobalTheory.Published.ChowFormIntExists
  chowCut : GlobalTheory.Published.ChowFormHyperplaneSection
  len : GlobalTheory.Published.ProperIntersectionLength

variable {F : Type} [Field F] [NumberField F]

def Split (T : Tuple F) (E : Type) [Field E] [Algebra F E] (s : Fin T.D → Fin T.N → E) : Prop :=
  ∀ x : Sp (AlgebraicClosure E) ⟶ (T.linSection E s).subscheme,
    x ≫ (T.linSection E s).subschemeι ≫ (T.toLinSys.baseChange E).str = spMap (algebraMap E (AlgebraicClosure E)) →
    ∃ x₀ : Sp E ⟶ (T.linSection E s).subscheme, x = spMap (algebraMap E (AlgebraicClosure E)) ≫ x₀

structure Coord {K : Type} [Field K] [NumberField K] (G : Geo K) {s : Fin G.D → Fin G.N → K} (hs : G.IsGood s) (δ : ℕ) where

  ev : ∀ j : ℕ, G.SecOn s j ≃ₗ[K] (Fin δ → K)

  y : Fin δ → Fin G.N → K

  c₂ : (K →+* ℂ) → Fin δ → ℝ
  y_ne : ∀ p, y p ≠ 0
  c₂_pos : ∀ σ p, 0 < c₂ σ p
  c₂_conj : ∀ σ p, c₂ ((starRingEnd ℂ).comp σ) p = c₂ σ p
  mul : ∀ (j : ℕ) (u : Fin G.N → K) (g : G.SecOn s j),
    ev (j + 1) (mulSecOn G.isLB₂ G.isLB (G.comb u) (Nat.cast_succ j).symm g) = fun p => (∑ k, u k * y p k) * ev j g p
  sq : ∀ (j : ℕ) (σ : K →+* ℂ) (m : ℕ) (c : Fin m → ℂ) (g : Fin m → G.SecOn s j),
    csq (hs.normOn j) σ c g =
      ∑ p, ‖∑ i, c i * σ (ev j (g i) p)‖ ^ 2 / (c₂ σ p * archSize (G.A σ) (fun k => σ (y p k)) ^ j) ^ 2

def Claim (X : Data F) (C h J : ℝ) : Prop :=
  0 ≤ X.z ∧ X.z ≤ 1 ∧
    (1 - X.z) * (X.T * h - 3 * ((X.D : ℝ) + 1) * |h| - J - C * (X.D : ℝ) ^ 2 * (X.logRho C h + Real.log X.T) -
        ((X.T : ℝ) + X.D + 1) * Real.log X.beta - ((X.T : ℝ) + (X.D : ℝ) ^ 2) * (X.g + 2)) -
      X.z * (X.T * (Real.log 2 + X.logRho C h + Real.log X.beta / 2) + Real.log X.LamD + Real.log X.LamT) ≤
    X.degM X.T / X.d

def RankLow : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (G : Geo F), IsNef F G.LA → IsBig F G.LA → ∀ T : ℕ,
    ((T - 1).choose G.D : ℤ) * G.del ≤ Module.finrank F (G.global T)

def KerRes : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (G : Geo K), IsNef K G.LA → IsBig K G.LA →
    ∀ (s : Fin G.D → Fin G.N → K), G.IsGood s → ∀ l : ℕ, G.D ≤ l + 1 →
      ∀ f ∈ Fil (G.ideal s) 1 (G.global (l + 1)), ∃ m : Fin G.D → G.Sec l, (∀ i, m i ∈ G.global l) ∧ f = ∑ i, G.mulW l (s i) (m i)

def FilMono : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (G : Geo K), IsNef K G.LA → IsBig K G.LA →
    ∀ (s : Fin G.D → Fin G.N → K), G.IsGood s → ∀ (a j l : ℕ) (h : j + a = l), G.D ≤ j →
      ∀ f ∈ Fil (G.ideal s) a (G.global l), ∃ m : MonoDeg (Fin G.D) a → G.Sec j,
        (∀ α, m α ∈ G.global j) ∧ f = ∑ α, mulPow G s h α (m α)

end GlobalTheory.HSCore
end
end

section

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT

namespace GlobalTheory.BigOn

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

section Any

variable {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

def scalOf (R : RealDat D A Ks) (F : Face D A) : (type_of% R.lam) × ℝ :=
  haveI : Nonempty ((type_of% R.lam) × ℝ) := ⟨(R.lam, 0)⟩
  Classical.epsilon fun q => (reScal R q.1 q.2).Char F

def charOf (R : RealDat D A Ks) (F : Face D A) : RealDat D A Ks := reScal R (scalOf R F).1 (scalOf R F).2

end Any

variable {J : CoreJ D} [Algebra J.Q.c.F D.what₂.LL] {R : RealDat D A J.Q.c.F}
  {κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)} {v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec}



def reFw (fw : FWTie J R κ v₀) (F : Face D A) : FWTie J (charOf R F) κ v₀ := { fw with }



def reOM {i : Fin D.R.m} (O : OMDat J.toCore R i Unit (fun _ => A.μ0)) (F : Face D A) :
    OMDat J.toCore (charOf R F) i Unit (fun _ => A.μ0) := { O with }

end GlobalTheory.BigOn

end
end

section

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links
open GlobalTheory.RunJoin GlobalTheory.RunIn GlobalTheory.FinalJoin GlobalTheory.FinalJoin2 GlobalTheory.RealIndexBound GlobalTheory.OnTies

namespace GlobalTheory.BigOn

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

structure CoreTies (L : SizeData₂ D) (EX : ErrX D) (J : CoreJ D) [Algebra J.Q.c.F D.what₂.LL] (R : RealDat D A J.Q.c.F) : Prop where
  laws : LawsCore J.toCore
  canon : J.Q.Canon
  rank : ∀ j, 1 ≤ (J.Q.Dw j).p + (J.Q.Dw j).q
  halfEX : HalfEX J.toCore EX
  field₁ : FieldOK0 D D.host.pde
  field₂ : FieldOK0 D D.host.pde'
  small : FieldSmall D L
  level : J.Q.l.Mb = ∏ PP ∈ R.Pg, PP.asIdeal
  oneHalf : ∃ Pk : ℕ → HeightOneSpectrum (𝓞 D.host.K), ∀ v ∈ R.twPl, ((ownAt D v : ℕ) : 𝓞 D.host.K) ∈ (Pk (ownAt D v)).asIdeal ∧
    ∀ PP ∈ placesOver R (R.mu v) (ownAt D v),
      (Pk (ownAt D v)).asIdeal.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) ≤ PP.asIdeal
  delVal : ∀ x, ((R.C.del.1 x : ℂˣ) : ℂ) ∈ FO D
  delVal' : ∀ x, ((R.C.del'.1 x : ℂˣ) : ℂ) ∈ FO D

def OwnPin {J : CoreJ D} (r : TwoRuns J G) : Prop :=
  ∀ v (j n : ℕ), InR D j → ((r.used v).full.dδ j n).pd = ownAt D v

def PageNum {L : SizeData₂ D} {Pm : ParameterChoice' D L} (Tp : ParamsT D L Pm) (x₁ : ℝ) : Prop :=
  SizesAt L ∧ Pm.CnW = 10 ∧ (∀ i, Real.log (D.host.g i) ≤ 9 * L.sc.L + 1) ∧ 1000 ≤ Tp.CP ∧ Tp.CP ^ 20 ≤ zBase L ∧ x₁ ≤ L.sc.x

def RunsHold {L : SizeData₂ D} {Pm : ParameterChoice' D L} (Tp : ParamsT D L Pm) (hK : DV.KapDef D) (EX : ErrX D) (CK : ℝ) {J : CoreJ D}
    (r : TwoRuns J G) : Prop :=
  ∀ v (h : LawsP (r.used v).full.toTop) (hinj : Function.Injective D.what₂.OtoLL) (j : ℕ) (hj : InR D j),
    HypC L (recPJ h j hj) ⟨CK, 20, Tp.CP, Tp.eP, Tp.CP, Tp.eP, 7⟩ Tp.CP Tp.eP 7 0 L.Ct
        (scalOfP (recB h.toLawsCore) hinj EX (ownAt D v) (kaR Tp hK j) (lR Tp hK j) (fR Tp hK j) Tp.TO) (kaR Tp hK j) (lR Tp hK j)
        (fR Tp hK j) Tp.TO Tp.nP Tp.nWn (LevelStarExponents.h0 L - 4) (nusR h j (lR Tp hK j)) ∧
      Concl (recPJ h j hj) (scalOfP (recB h.toLawsCore) hinj EX (ownAt D v) (kaR Tp hK j) (lR Tp hK j) (fR Tp hK j) Tp.TO)
        (kaR Tp hK j) (lR Tp hK j) (fR Tp hK j) Tp.TO (nusR h j (lR Tp hK j))
        ((recPJ h j hj).rk (kaR Tp hK j) ((recB h.toLawsCore).Mlat j (kaR Tp hK j)) * D.R.f * D.R.m * L.sc.b * L.de2)

theorem isDelta_delAt_ownAt (C : Formalism.L2.Host.CharFrame D) (v : HeightOneSpectrum (𝓞 D.what₂.LL)) :
    Formalism.L2.Host.IsDelta (H := D.host) (ownAt D v) (C.delAt (Formalism.EigenvalueLevelCeiling.plc v)) := by
  unfold ownAt Formalism.L2.Host.CharFrame.delAt
  split_ifs
  exacts [C.isDel', C.isDel]

namespace CoreTies

variable {L : SizeData₂ D} {EX : ErrX D} {J : CoreJ D} [Algebra J.Q.c.F D.what₂.LL] {R : RealDat D A J.Q.c.F}

theorem inj (h : CoreTies L EX J R) : Function.Injective D.what₂.OtoLL := h.field₁.full.1

theorem fieldAt (h : CoreTies L EX J R) (v : HeightOneSpectrum (𝓞 D.what₂.LL)) : FieldOK0 D (ownAt D v) := by
  unfold ownAt
  split_ifs
  exacts [h.field₂, h.field₁]

theorem delAt_mem (h : CoreTies L EX J R) (l : ℕ) (x) : (((R.C.delAt l).1 x : ℂˣ) : ℂ) ∈ FO D := by
  unfold Formalism.L2.Host.CharFrame.delAt
  split_ifs
  exacts [h.delVal' x, h.delVal x]

end CoreTies


omit [Group G] [Fintype G] in
theorem ownPin_of {J : CoreJ D} {r : TwoRuns J G} (h₁ : ∀ j n : ℕ, InR D j → (r.first.full.dδ j n).pd = D.host.pde)
    (h₂ : ∀ j n : ℕ, InR D j → (r.second.full.dδ j n).pd = D.host.pde') : OwnPin r := by
  intro v j n hj
  by_cases h : Formalism.EigenvalueLevelCeiling.plc v = D.host.pde
  · rw [show r.used v = r.second from if_pos h, show ownAt D v = D.host.pde' from if_pos h]
    exact h₂ j n hj
  · rw [show r.used v = r.first from if_neg h, show ownAt D v = D.host.pde from if_neg h]
    exact h₁ j n hj

end GlobalTheory.BigOn

end
end

section

noncomputable section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid
open scoped TensorProduct Classical

namespace GlobalTheory.LKDef

variable {p : ℕ} [Fact p.Prime]

structure DPair (G : HTGroup p) where

  β : G.Cˣ

  γ : G.Cˣ

  c : ℚˣ
  sym : sh G β = β
  sim : (γ : G.C) * β * sh G γ = algebraMap ℚ G.C c * β
  reg : (minpoly G.F (γ : G.C)).natDegree = G.n ∧ (minpoly G.F (γ : G.C)).Separable
  trivAf : ∃ (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ), Triv G (AfP p) β x t

  posR : ∀ v : InfinitePlace G.F, ∀ x : Fin G.n → ℂ, x ≠ 0 →
    (sigPosH (G.gram_herm v) = 1 → 0 < (star x ⬝ᵥ ((G.gram v * G.psi v ((β⁻¹ : G.Cˣ) : G.C)) *ᵥ x)).re) ∧
    (sigPosH (G.gram_herm v) ≠ 1 → (star x ⬝ᵥ ((G.gram v * G.psi v ((β⁻¹ : G.Cˣ) : G.C)) *ᵥ x)).re < 0)

namespace DPair

variable {G : HTGroup p}

def pol (P : DPair G) : Polynomial G.F := minpoly G.F (P.γ : G.C)

def Rel (P Q : DPair G) : Prop :=
  ∃ (y : G.Cˣ) (s : ℚ), 0 < s ∧ (Q.β : G.C) = algebraMap ℚ G.C s * (y * P.β * sh G y) ∧ Q.γ = y * P.γ * y⁻¹

def cent (P : DPair G) : Subgroup (G.Cˣ × ℚˣ) where
  carrier := {y | y.1 * P.γ = P.γ * y.1 ∧ (y.1 : G.C) * P.β * sh G y.1 = algebraMap ℚ G.C y.2 * P.β}
  one_mem' := ⟨by simp, by simp [sh]⟩
  mul_mem' := by
    rintro ⟨y, s⟩ ⟨y', s'⟩ ⟨h1, h2⟩ ⟨h1', h2'⟩
    refine ⟨?_, ?_⟩
    · change y * y' * P.γ = P.γ * (y * y')
      change y * P.γ = P.γ * y at h1
      change y' * P.γ = P.γ * y' at h1'
      rw [mul_assoc, h1', ← mul_assoc, h1, mul_assoc]
    · change (y : G.C) * P.β * sh G y = algebraMap ℚ G.C s * P.β at h2
      change (y' : G.C) * P.β * sh G y' = algebraMap ℚ G.C s' * P.β at h2'
      change ((y * y' : G.Cˣ) : G.C) * P.β * sh G ((y * y' : G.Cˣ) : G.C) =
        algebraMap ℚ G.C ((s * s' : ℚˣ) : ℚ) * P.β
      have e : sh G ((y * y' : G.Cˣ) : G.C) = sh G y' * sh G y := by
        simp only [sh, Units.val_mul, map_mul, MulOpposite.unop_mul]
      rw [e, Units.val_mul, Units.val_mul, map_mul]
      calc (y : G.C) * y' * P.β * (sh G y' * sh G y) = y * (y' * P.β * sh G y') * sh G y := by
            simp only [mul_assoc]
        _ = algebraMap ℚ G.C s' * (y * P.β * sh G y) := by
            rw [h2']; simp only [← Algebra.smul_def, mul_smul_comm, smul_mul_assoc]
        _ = _ := by rw [h2, ← mul_assoc, ← map_mul, ← map_mul, mul_comm (s' : ℚ)]
  inv_mem' := by
    rintro ⟨y, s⟩ ⟨h1, h2⟩
    change y * P.γ = P.γ * y at h1
    change (y : G.C) * P.β * sh G y = algebraMap ℚ G.C s * P.β at h2
    refine ⟨?_, ?_⟩
    · change y⁻¹ * P.γ = P.γ * y⁻¹
      rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, h1, mul_inv_cancel_right]
    · change ((y⁻¹ : G.Cˣ) : G.C) * P.β * sh G ((y⁻¹ : G.Cˣ) : G.C) =
        algebraMap ℚ G.C ((s⁻¹ : ℚˣ) : ℚ) * P.β
      have e : sh G y * sh G ((y⁻¹ : G.Cˣ) : G.C) = 1 := by
        simp only [sh]
        rw [← MulOpposite.unop_mul, ← map_mul, Units.inv_mul, map_one, MulOpposite.unop_one]
      have hs : algebraMap ℚ G.C ((s⁻¹ : ℚˣ) : ℚ) * algebraMap ℚ G.C (s : ℚ) = 1 := by
        rw [← map_mul, Units.inv_mul, map_one]
      calc ((y⁻¹ : G.Cˣ) : G.C) * P.β * sh G ((y⁻¹ : G.Cˣ) : G.C)
          = algebraMap ℚ G.C ((s⁻¹ : ℚˣ) : ℚ) * (((y⁻¹ : G.Cˣ) : G.C) * (algebraMap ℚ G.C (s : ℚ) * P.β) *
              sh G ((y⁻¹ : G.Cˣ) : G.C)) := by
            rw [← mul_assoc, ← mul_assoc, ← mul_assoc, Algebra.commutes ((s⁻¹ : ℚˣ) : ℚ), mul_assoc ((y⁻¹ : G.Cˣ) : G.C) _ (algebraMap ℚ G.C (s : ℚ)), hs, mul_one]
        _ = algebraMap ℚ G.C ((s⁻¹ : ℚˣ) : ℚ) * ((((y⁻¹ : G.Cˣ) : G.C) * y) * P.β *
              (sh G y * sh G ((y⁻¹ : G.Cˣ) : G.C))) := by
            rw [← h2]; simp only [mul_assoc]
        _ = _ := by rw [Units.inv_mul, e, one_mul, mul_one]

def self (P : DPair G) : P.cent := ⟨(P.γ, P.c), rfl, P.sim⟩

def toAf (P : DPair G) (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (hx : Triv G (AfP p) P.β x t) : P.cent →* G.GAf :=
  MonoidHom.codRestrict
    ((((MulAut.conj x).toMonoidHom.comp (Units.map (inC G (AfP p)).toMonoidHom)).prodMap
      (Units.map (algebraMap ℚ (AfP p)).toMonoidHom)).comp P.cent.subtype) _ fun y => by
      have h := congrArg (inC G (AfP p)) y.2.2
      rw [map_mul, map_mul, map_mul] at h
      have e1 : inC G (AfP p) (sh G y.1.1) = (starT G.star (AfP p) (inC G (AfP p) y.1.1)).unop :=
        (starT_tmul G.star (AfP p) 1 _).symm
      have e2 : inC G (AfP p) (algebraMap ℚ G.C y.1.2) =
          algebraMap (AfP p) (AfP p ⊗[ℚ] G.C) (algebraMap ℚ (AfP p) y.1.2) := by
        rw [← IsScalarTower.algebraMap_apply]
        exact (Algebra.TensorProduct.includeRight : G.C →ₐ[ℚ] AfP p ⊗[ℚ] G.C).commutes _
      rw [e1, e2] at h
      exact conj_mul_star (starT G.star (AfP p)) (inC G (AfP p) P.β) x
        (Units.map (inC G (AfP p)).toMonoidHom y.1.1) t _ hx h

def atP (P : DPair G) : Gp G := locC G (P.γ, P.c)

def toQr (P : DPair G) (r : ℕ) (z : Gr G r) : P.cent →* Gr G r :=
  ((carry G r z).comp (locC G)).comp P.cent.subtype

def termAt (P : DPair G) (Kf : Subgroup G.GAf) (f : G.GAf → ℂ) (r : ℕ) (K : Subgroup (Gr G r)) (φ : Gr G r → ℂ)
    (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (hx : Triv G (AfP p) P.β x t) (δ z : Gr G r) : ℂ :=
  GlobalTheory.LKCount.pointSum (P.toAf x t hx) (P.toQr r z) (sigG G r) Kf K (P.toAf x t hx P.self) δ f φ

def term (P : DPair G) (Kf : Subgroup G.GAf) (f : G.GAf → ℂ) (r : ℕ) (K : Subgroup (Gr G r)) (φ : Gr G r → ℂ) : ℂ :=
  if h : ∃ dz : Gr G r × Gr G r, IsNrm G r P.atP dz.1 dz.2 then
    P.termAt Kf f r K φ P.trivAf.choose P.trivAf.choose_spec.choose P.trivAf.choose_spec.choose_spec
      h.choose.1 h.choose.2
  else 0

open Matrix NumberField in
open scoped TensorProduct Classical in
variable {p : ℕ} [Fact p.Prime] in
variable {G : _root_.GlobalTheory.LKTrip.HTGroup p} in
private theorem lkMid_sh_mul_eq_sh_mul_sh_rev (a b : G.C) :
    _root_.GlobalTheory.LKMid.sh G (a * b) =
      _root_.GlobalTheory.LKMid.sh G b * _root_.GlobalTheory.LKMid.sh G a := by
  simp only [_root_.GlobalTheory.LKMid.sh, map_mul, MulOpposite.unop_mul]

open Matrix NumberField in
open scoped TensorProduct Classical in
variable {p : ℕ} [Fact p.Prime] in
variable {G : _root_.GlobalTheory.LKTrip.HTGroup p} in
private theorem lkMid_sh_mul_sh_units_inv_eq_one (y : (G.C)ˣ) :
    _root_.GlobalTheory.LKMid.sh G y *
      _root_.GlobalTheory.LKMid.sh G ((y⁻¹ : (G.C)ˣ) : G.C) = 1 := by
  rw [← lkMid_sh_mul_eq_sh_mul_sh_rev, Units.inv_mul, _root_.GlobalTheory.LKMid.sh_one_eq]


open Matrix NumberField in
open scoped TensorProduct Classical in
variable {p : ℕ} [Fact p.Prime] in
variable {G : _root_.GlobalTheory.LKTrip.HTGroup p} in
theorem _root_.GlobalTheory.LKDef.DPair.rel_equivalence (G : _root_.GlobalTheory.LKTrip.HTGroup p) :
    Equivalence (_root_.GlobalTheory.LKDef.DPair.Rel (G := G)) := by
  refine ⟨fun P => ?_, fun {P₁ P₂} h => ?_, fun {P₁ P₂ P₃} h h' => ?_⟩
  · refine ⟨1, 1, one_pos, ?_, by simp⟩
    simp [_root_.GlobalTheory.LKMid.sh_one_eq]
  · obtain ⟨y, s, hs, hβ, hγ⟩ := h
    refine ⟨y⁻¹, s⁻¹, inv_pos.mpr hs, ?_, ?_⟩
    · rw [hβ]
      simp only [← Algebra.smul_def, mul_smul_comm, smul_mul_assoc, smul_smul,
        inv_mul_cancel₀ hs.ne', one_smul]
      simp only [mul_assoc, Units.inv_mul_cancel_left, lkMid_sh_mul_sh_units_inv_eq_one, mul_one]
      rw [mul_inv_cancel₀ hs.ne', one_smul]
    · rw [hγ]; group
  · obtain ⟨y, s, hs, hβ, hγ⟩ := h
    obtain ⟨y', s', hs', hβ', hγ'⟩ := h'
    refine ⟨y' * y, s' * s, mul_pos hs' hs, ?_, ?_⟩
    · rw [hβ', hβ, Units.val_mul, lkMid_sh_mul_eq_sh_mul_sh_rev]
      simp only [← Algebra.smul_def, mul_smul_comm, smul_mul_assoc, smul_smul, mul_assoc]
      rw [mul_comm s s']
    · rw [hγ', hγ]; group

theorem pol_eq_of_rel {P Q : DPair G} (h : P.Rel Q) : Q.pol = P.pol := by
  obtain ⟨y, s, _, _, hγ⟩ := h
  have h := minpoly.algEquiv_eq (Pair.innerAlgEquiv G.F y) (P.γ : G.C)
  simp only [pol, hγ, Units.val_mul]
  exact h


open Matrix NumberField in
open scoped TensorProduct Classical in
variable {p : ℕ} [Fact p.Prime] in
variable {G : _root_.GlobalTheory.LKTrip.HTGroup p} in
theorem _root_.GlobalTheory.LKDef.DPair.mk_eq_iff (P Q : _root_.GlobalTheory.LKDef.DPair G) :
    Quot.mk (_root_.GlobalTheory.LKDef.DPair.Rel (G := G)) P = Quot.mk _ Q ↔
      P.Rel Q :=
  ⟨fun h => (_root_.GlobalTheory.LKDef.DPair.rel_equivalence G).eqvGen_iff.mp (Quot.eqvGen_exact h),
    Quot.sound⟩


open Matrix NumberField in
open scoped TensorProduct Classical in
variable {p : ℕ} [Fact p.Prime] in
variable {G : _root_.GlobalTheory.LKTrip.HTGroup p} in
theorem _root_.GlobalTheory.LKDef.DPair.rel_out (P : _root_.GlobalTheory.LKDef.DPair G) :
    P.Rel
      (Quot.out (Quot.mk (_root_.GlobalTheory.LKDef.DPair.Rel (G := G)) P)) :=
  (_root_.GlobalTheory.LKDef.DPair.mk_eq_iff P _).mp (Quot.out_eq _).symm

end DPair

def DCls (G : HTGroup p) : Type := Quot (DPair.Rel (G := G))

def dSumIrr (G : HTGroup p) (wt : Polynomial G.F → ℂ) (Kf : Subgroup G.GAf) (f : G.GAf → ℂ) (r : ℕ)
    (K : Subgroup (Gr G r)) (φ : Gr G r → ℂ) : ℂ :=
  ∑ᶠ q : DCls G, if Irreducible (Quot.out q).pol then wt (Quot.out q).pol * (Quot.out q).term Kf f r K φ else 0

namespace Example

open GlobalTheory.LKTrip.Example GlobalTheory.LKMid.Example

end Example

end GlobalTheory.LKDef
end
end
