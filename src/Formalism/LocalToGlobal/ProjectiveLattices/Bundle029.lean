module

public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle011
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle028
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle009
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle014
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle025
public import Formalism.LocalToGlobal.ProjectiveLattices.ThGerm
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle023
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
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
import Mathlib.Tactic.ReduceModChar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.TheoremA

@[expose] public section

section

noncomputable section

namespace Formalism.L2.Pj

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}

structure Unf (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) : Type 1 where

  Comp : Type
  [fin : Fintype Comp]

  X : Comp → Data E r

  un : ∀ k, (X k).dom → FrPt Xo c (CAt σ)

attribute [instance] Unf.fin

variable {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ}

def gxFst {S : Type} [CommRing S] (x : Sp S ⟶ Xo.X) : Gx x ⟶ Xo.univ.t.G.left :=
  (CartesianMonoidalCategory.snd (Over.mk x) Xo.univ.t.G).left

def gxSnd {S : Type} [CommRing S] (x : Sp S ⟶ Xo.X) : Gx x ⟶ Sp S :=
  (CartesianMonoidalCategory.fst (Over.mk x) Xo.univ.t.G).left

def toC {K : Type} [Field K] {σ : K →+* ℂ} (z : CAt σ) : ℂ := z


open Classical in
def rdU (U : Unf Xo c σ r) : Rul Xo c →ₛₗ[σ] FDSec U.X where
  toFun f := fun k x => if h : x ∈ (U.X k).dom then toC (evR Xo c f (U.un k ⟨x, h⟩)) else 0
  map_add' f g := by
    funext k x
    simp only [Pi.add_apply]
    split_ifs with h
    · have e := evalAt_add (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) f g (U.un k ⟨x, h⟩)
      exact e
    · simp
  map_smul' a f := by
    funext k x
    simp only [Pi.smul_apply, smul_eq_mul]
    split_ifs with h
    · have e := evalAt_smul (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) a f (U.un k ⟨x, h⟩)
      exact e
    · simp

def relab (c : Coeff l) (σ : c.F →+* ℂ) (τ : E →+* ℂ) : E →+* ℂ := σ.comp (embF c τ)

def GoodEmb (c : Coeff l) (σ : c.F →+* ℂ) : Prop :=
  (σ.comp (IntermediateField.inclusion c.le).toRingHom) (baseKA l).ρ = H.rt0


open Classical in
def laU (U : Unf Xo c σ r) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (k : U.Comp) : Wt (U.X k).Ψ r :=
  fun τ j => if (U.X k).p0 ≤ (j : ℕ) then
      (a (Function.invFun (relab c σ) τ.1, (j : ℕ) - (U.X k).p0) : ℤ) + ((n / 2 : ℕ) : ℤ)
    else -(a (Function.invFun (relab c σ) (conjEmb τ.1), (U.X k).p0 - 1 - (j : ℕ)) : ℤ) - ((n / 2 : ℕ) : ℤ)


open Classical in
def perFr (X : Data E r) (x : Frame X.Ψ r) (v : Fin r → E) (τ : E →+* ℂ) (i : ℕ) : ℂ :=
  if h : τ ∈ X.Ψ then
    (if hi : X.p0 + i < r then ((mat x ⟨τ, h⟩)⁻¹.mulVec (Data.emb τ v)) ⟨X.p0 + i, hi⟩ else 0)
  else if h' : conjEmb τ ∈ X.Ψ then
    (if hj : X.p0 - 1 - i < r then
      hermC (conjEmb τ) X.Gm (col (mat x ⟨conjEmb τ, h'⟩) ⟨X.p0 - 1 - i, hj⟩) (Data.emb (conjEmb τ) v) else 0)
  else 0

def IsUnf (U : Unf Xo c σ r) : Prop :=
  r = Dw.p + Dw.q ∧ (∀ k, (U.X k).p0 = Dw.q ∧ ∀ τ : E →+* ℂ, τ ∈ (U.X k).Ψ ↔ τ (H.rt : E) = H.rt0) ∧
    (∀ y : FrPt Xo c (CAt σ), ∃ k, ∃ x : (U.X k).dom, ∃ t : Ix Dw → (CAt σ)ˣ, FrBor t (U.un k x) y) ∧
    (∀ k k' (x : (U.X k).dom) (x' : (U.X k').dom), (∃ t : Ix Dw → (CAt σ)ˣ, FrBor t (U.un k x) (U.un k' x')) ↔
      ∃ γ ∈ (U.X k).Γ, ∃ b ∈ Bor (U.X k).Ψ r,
        (⟨k', x'.1⟩ : Σ k, Frame (U.X k).Ψ r) = ⟨k, rmul (lact γ x.1) b⟩) ∧
    (∀ a n, Dom a n → ∀ f ∈ sec Xo c a n, ∀ k, (U.X k).IsSec (laU U a n k) (rdU U f k)) ∧
    ∃ (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ))
      (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1))
      (ik : U.Comp → Fin F.n) (φ : ∀ k, (F.Di (ik k)).La ≃ₗ[𝓞 E] (U.X k).Λ),
      (∀ k a b, (((F.Di (ik k)).EF a b : ℤ) : ℚ) =
        Algebra.trace ℚ E (-(U.X k).ξ0 * herm (U.X k).Gm (φ k a : Fin r → E) (φ k b))) ∧
      ∀ k (x : (U.X k).dom), ∃ Pm : (F.Di (ik k)).La →+ (Fin g → ℂ),
        (∀ a j, Pm a j = perFr (U.X k) x.1 (φ k a : Fin r → E) (relab c σ (e j).1) (e j).2) ∧
        IsPeriod (F.Di (ik k)) (fun j => relab c σ (e j).1) Pm ∧ (U.un k x).x = F.u (ik k) Pm ∧
        (∀ τ (i : Fin (Dw.mult τ)), IsDerivAt0 (fun z => (F.ex (ik k) Pm z).left) (Pi.single (e.symm ⟨τ, i⟩) 1)
          ((U.un k x).u τ i)) ∧
        ((∀ τ' i', ‖dmin (U.X k).Gm x.1 τ' i'‖ = 1) →
          ∃ (Hm : Matrix (Fin g) (Fin g) ℂ) (χl : (Fin g → ℂ) → ℂ) (fr : Xo.univ.t.PP.L.ι → (Fin g → ℂ) → ℂ)
            (θ : (Fin g → ℂ) → ℂ) (Fd : Set (Fin g → ℂ)),
            Hm.IsHermitian ∧ (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) ∧
            (∀ a b, (hermForm Hm (Pm a) (Pm b)).im = (F.Di (ik k)).EF a b) ∧
            (∀ j, DifferentiableOn ℂ (fr j) {z | ⊤ ≤ (F.ex (ik k) Pm z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j}) ∧
            (∀ j z, ⊤ ≤ (F.ex (ik k) Pm z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j → fr j z ≠ 0) ∧
            (∀ j j' z, ⊤ ≤ (F.ex (ik k) Pm z).left ⁻¹ᵁ (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U j') →
              fr j z = valAt' (F.ex (ik k) Pm z).left (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U j')
                (Xo.univ.t.PP.L.g j j').val * fr j' z) ∧
            (∀ j, ⊤ ≤ (F.ex (ik k) Pm 0).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
              fr j 0 = valAt' (U.un k x).x ((Xo.univ.t.PP.L.pull (eSec Xo.univ.t.G)).U (fun _ => j))
                (Xo.univ.t.PP.rig.s (fun _ => j)).val) ∧
            (∀ a j z, ‖χl (Pm a)‖ = 1 ∧ (⊤ ≤ (F.ex (ik k) Pm z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
              fr j z = χl (Pm a) * Complex.exp (Real.pi * hermForm Hm z (Pm a) +
                Real.pi / 2 * hermForm Hm (Pm a) (Pm a)) * fr j (z + Pm a))) ∧
            (∀ j z (pt : Sp ℂ ⟶ Gx (U.un k x).x),
              pt ≫ gxFst (U.un k x).x = (F.ex (ik k) Pm z).left →
              pt ≫ gxSnd (U.un k x).x = 𝟙 (Sp ℂ) →
              ⊤ ≤ (F.ex (ik k) Pm z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
              valAt' pt ((PPx (U.un k x).x).U (fun _ => j)) ((U.un k x).s.f (fun _ => j)) = θ z * fr j z) ∧
            MeasureTheory.IsAddFundamentalDomain Pm.range Fd MeasureTheory.volume ∧
            (∫ z in Fd, ‖θ z‖ ^ 2 * Real.exp (-Real.pi * (hermForm Hm z z).re)) /
              (MeasureTheory.volume Fd).toReal = 1)

end Formalism.L2.Pj
end
end

section

noncomputable section

namespace Formalism.L2.Pj

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  (Xo : Moduli Dw l) (c : Coeff l)

def trivCls : ∀ (T : CDVR) (ι : c.F →+* T.Fr), IntFr Xo c T ι → Prop :=
  fun T ι _ => ∀ a : c.F, a ≠ 0 → ∃ u : T.Vˣ, algebraMap T.V T.Fr (u : T.V) = ι a

structure QPt where
  T : CDVR
  ι : c.F →+* T.Fr
  y : IntFr Xo c T ι
  triv : trivCls Xo c T ι y

def ordQ (q : QPt Xo c) (f : Rul Xo c) : EReal := nval q.T.V 1 (evI q.y f)

def RegularityR1Quotient (C : ((E →+* ℂ) × ℕ → ℕ) → ℕ → Submodule c.F (Rul Xo c)) : Prop :=
  ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), ∀ f ∈ C a n,
    (∃ la : HeightOneSpectrum (𝓞 c.F), ∀ v ∈ valSet Xo c (algCls Xo c) la, 0 ≤ v f) →
      ∀ q : QPt Xo c, 0 ≤ ordQ Xo c q f

def RegularityR2Quotient (C : ((E →+* ℂ) × ℕ → ℕ) → ℕ → Submodule c.F (Rul Xo c)) : Prop :=
  ∀ (aL : (E →+* ℂ) × ℕ → ℕ) (nL : ℕ) (aE : (E →+* ℂ) × ℕ → ℕ) (nE k : ℕ) (ws : Fin k → Rul Xo c)
    (et : Rul Xo c) (c' : ℝ), 0 ≤ c' → (∀ i, ws i ∈ C aL nL) → et ∈ C aE nE →
    (∃ (la : HeightOneSpectrum (𝓞 c.F)) (nu : ℝ), ∀ v ∈ valSet Xo c (algCls Xo c) la,
      0 ≤ v et ∧ (∃ i, v (ws i) ≠ ⊤) ∧ (v et ≠ ⊤ → (⨅ i, v (ws i)) ≤ (nu : EReal) + (c' : EReal) * v et)) →
    ∀ q : QPt Xo c, 0 ≤ ordQ Xo c q et ∧
      (ordQ Xo c q et ≠ ⊤ → (⨅ i, ordQ Xo c q (ws i)) ≤ (c' : EReal) * ordQ Xo c q et)

end Formalism.L2.Pj
end
end

section

noncomputable section

namespace Formalism.L2.Pj

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.T0

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem vAtV_mem_valSet {cls cls' : ∀ (T : CDVR) (io : c.F →+* T.Fr), IntFr Xo c T io → Prop}
    (hc : ∀ T io y, cls T io y → cls' T io y) {PY : Type}
    {lies : ∀ (T : CDVR) (io : c.F →+* T.Fr), IntFr Xo c T io → PY → Prop}
    {la : HeightOneSpectrum (𝓞 c.F)} (y : PtV Xo c cls PY lies la) :
    vAtV y ∈ valSet Xo c cls' la := by
  unfold vAtV valSet
  refine ⟨⟨((y.1).1, ()), ?_⟩, rfl⟩
  obtain ⟨T, io, e, hO, y1, hcl, eta, -, hy⟩ := y.2
  refine ⟨T, io, e, hO, y1, hc T io y1 hcl, (), trivial, ?_⟩
  rw [hy]
  rfl

theorem valC_add (h : GenFrEx Xo c) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (f g : Rul Xo c) (Z : Comp Xo c) :
    valC h a n (f + g) Z = valC h a n f Z + valC h a n g Z := by
  simp only [valC, evC, evR]
  rw [evalAt_add, AddMonoidAlgebra.single_add]

theorem valC_zero (h : GenFrEx Xo c) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (Z : Comp Xo c) :
    valC h a n 0 Z = 0 := by
  simp only [valC, evC, evR]
  rw [evalAt_zero, AddMonoidAlgebra.single_zero]

theorem valC_smul_ct (h : GenFrEx Xo c) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (t : c.F) (f : Rul Xo c) (Z : Comp Xo c) :
    valC h a n (t • f) Z = algebraMap c.F (AC Z) t * valC h a n f Z := by
  simp only [valC, evC, evR]
  rw [evalAt_smul, ← Algebra.smul_def, ← Algebra.smul_def, AddMonoidAlgebra.smul_single]

theorem evC_ne_zero_of_valC {h : GenFrEx Xo c} {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ} {f : Rul Xo c} {Z : Comp Xo c}
    (hf : valC h a n f Z ≠ 0) : evC h Z f ≠ 0 := by
  intro h0
  apply hf
  unfold valC
  rw [h0, AddMonoidAlgebra.single_zero]

end Formalism.L2.Pj
end
end

section

noncomputable section

namespace Formalism.L2.Pj

open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {D : D7} (Q : Par D)

structure In66 : Type 1 where
  P : ModuliIntegralCharts.Prov D
  dat : ℕ → P.Dat
  Tw : ∀ j p, PointsOfFlagModel.Tower p (Q.Xo j) Q.c
  rel : ∀ j p, (P.loc (dat j) p).Pt (P.loc (dat j) p).YY → PointsOfFlagModel.Pt (Tw j p) .yy → Prop

namespace In66

variable {Q} (G : In66 Q)

abbrev PY (j p : ℕ) : Type := (G.P.loc (G.dat j) p).Pt (G.P.loc (G.dat j) p).YY

def PinDat : Prop := ∀ j, 1 ≤ j → j < D.R.m → G.P.rk (G.dat j) = D.R.r ∧ G.P.jj (G.dat j) = (D.R.sigW j).1

def PinTower : Prop := ∀ j, 1 ≤ j → j < D.R.m → ∀ p, p.Prime → PointsOfFlagModel.TowerAt (G.Tw j p)

def IsAlgPt (j : ℕ) (la : HeightOneSpectrum (𝓞 Q.c.F)) (z : PointsOfFlagModel.Pt (G.Tw j (WeightAlgebra.resCh la)) .yy) : Prop :=
  ∃ (T : CDVR) (io : Q.c.F →+* T.Fr) (e : ℕ) (y : IntFr (Q.Xo j) Q.c T io), OverLa la T.V io e ∧
    algCls (Q.Xo j) Q.c T io y ∧ LiesOverBaseChange la (G.Tw j (WeightAlgebra.resCh la)) T io y z

def HasData : Prop := ∀ j, 1 ≤ j → j < D.R.m → ∀ la z, G.IsAlgPt j la z →
  Nonempty (DatAt ((G.Tw j (WeightAlgebra.resCh la)).Y z.1) z.2.2.1)

def PinPts : Prop := ∀ j, 1 ≤ j → j < D.R.m → ∀ la z, G.IsAlgPt j la z →
  (∃ η, G.rel j _ η z) ∧ ∀ η, G.rel j _ η z → (G.P.loc (G.dat j) _).fld η = PointsOfFlagModel.fld z

def PinLat : Prop := ∀ j, 1 ≤ j → j < D.R.m → ∀ la z, G.IsAlgPt j la z → ∀ η, G.rel j _ η z →
  ∀ A : DatAt ((G.Tw j (WeightAlgebra.resCh la)).Y z.1) z.2.2.1,
    ∃ e : (G.P.loc (G.dat j) _).Ylat η ≃ₗ[𝓞 D.host.E] A.Ylat,
      ∀ a b, A.beta (e a) (e b) = (G.P.loc (G.dat j) _).be η a b

def BaseChange : Prop := ∀ j, 1 ≤ j → j < D.R.m →
  ∀ (la : HeightOneSpectrum (𝓞 Q.c.F)) (T : CDVR) (io : Q.c.F →+* T.Fr) (e : ℕ), OverLa la T.V io e →
    ∀ y : IntFr (Q.Xo j) Q.c T io, algCls (Q.Xo j) Q.c T io y →
      ∃ z, LiesOverBaseChange la (G.Tw j (WeightAlgebra.resCh la)) T io y z

def lies (j : ℕ) (la : HeightOneSpectrum (𝓞 Q.c.F)) (T : CDVR) (io : Q.c.F →+* T.Fr)
    (y : IntFr (Q.Xo j) Q.c T io) (η : G.PY j (WeightAlgebra.resCh la)) : Prop :=
  j < D.R.m → ∃ z, G.rel j (WeightAlgebra.resCh la) η z ∧ LiesOverBaseChange la (G.Tw j (WeightAlgebra.resCh la)) T io y z

end In66

theorem resCh_prime {K : Type} [Field K] [NumberField K] (la : HeightOneSpectrum (𝓞 K)) : (WeightAlgebra.resCh la).Prime := by
  unfold WeightAlgebra.resCh
  haveI := la.isPrime
  haveI : Finite (𝓞 K ⧸ la.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot la.asIdeal la.ne_bot
  first
  | exact CharP.char_is_prime (𝓞 K ⧸ la.asIdeal) _
  | exact (CharP.char_is_prime_or_zero (𝓞 K ⧸ la.asIdeal) _).resolve_right
      (ringChar.char_ne_zero_of_finite _)

variable {Q}

theorem In66.liesTotal (G : In66 Q) (h1 : G.PinPts) (h2 : G.BaseChange) {j : ℕ} (hj : InR D j) :
    LiesTotal (Q.Xo j) Q.c (algCls (Q.Xo j) Q.c) (fun la => G.PY j (WeightAlgebra.resCh la)) (G.lies j) := by
  intro la T io e ho y hy
  by_cases hm : j < D.R.m
  · obtain ⟨z, hz⟩ := h2 j hj.1 hm la T io e ho y hy
    obtain ⟨η, hη⟩ := (h1 j hj.1 hm la z ⟨T, io, e, y, ho, hy, hz⟩).1
    exact ⟨η, fun _ => ⟨z, hη, hz⟩⟩
  · exact ⟨(G.P.ex (G.dat j) (WeightAlgebra.resCh la)).yEta
      (Classical.choice ((G.P.ex (G.dat j) (WeightAlgebra.resCh la)).genNe _)), fun h => absurd h hm⟩

end Formalism.L2.Pj
end
end

section

noncomputable section

namespace Formalism.L2.Pj

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.MainNotions

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} (Xo : Moduli Dw l) (c : Coeff l)

def NabUniq : Prop :=
  ∀ (_ : StarRing (𝓞 E)) (nab nab' : NabV Xo c), IsNab Xo c nab → IsNab Xo c nab' →
    ∀ a n, Dom a n → thGen Xo c nab a n = thGen Xo c nab' a n

def DatIndep : Prop :=
  ∀ (la : HeightOneSpectrum (𝓞 c.F)) (Tw Tw' : PointsOfFlagModel.Tower (WeightAlgebra.resCh la) Xo c), PointsOfFlagModel.TowerAt Tw → PointsOfFlagModel.TowerAt Tw' →
    ∀ (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ) (y : IntFr Xo c T io), OverLa la T.V io e → algCls Xo c T io y →
      ∀ z z', LiesOverBaseChange la Tw T io y z → LiesOverBaseChange la Tw' T io y z' →
        ∀ (A : DatAt (Tw.Y z.1) z.2.2.1) (A' : DatAt (Tw'.Y z'.1) z'.2.2.1),
          ∃ f : A.Ylat ≃ₗ[𝓞 E] A'.Ylat, ∀ a b, A'.beta (f a) (f b) = A.beta a b

end Formalism.L2.Pj
end
end
