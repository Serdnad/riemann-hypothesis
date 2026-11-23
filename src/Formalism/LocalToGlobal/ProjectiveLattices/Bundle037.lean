module

public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle029
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle034
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle033
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle012
public import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
public import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle002
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle014
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle007
public import Formalism.LocalToGlobal.ProjectiveLattices.SpanRatSmulMem
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
import Formalism.SharpRestriction.Divisibility.AbelianOpenPart.AbelianAt
import Mathlib.Tactic.ReduceModChar

@[expose] public section

section

noncomputable section

namespace Formalism.L2.Pj

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta
  Formalism.MainNotions.DIV.Cons
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

structure Top (D : D7) : Type 1 extends Core D where
  G : In66 Q
  nab : ∀ j, NabV (Q.Xo j) Q.c
  dδ : ∀ j n, DeltaDat (Q.Xo j) Q.c n

variable {D : D7}

def badN (D : D7) : ℕ := D.host.QS * D.host.q * D.host.d * ∏ p ∈ D.host.levelPrimes, p

def wEt (D : D7) (j i : ℕ) : WeightFamilies.Wt D j :=
  WeightAlgebra.wscalar D j (WeightAlgebra.g0 D * i) (by unfold WeightAlgebra.g0; exact ⟨5 ^ 4 * D.R.r * i, by ring⟩)

structure LawsP (T : Top D) : Prop extends LawsCore T.toCore where

  allTest : ∀ j, InR D j → AllTest (T.Q.Xo j) T.Q.c

  reg : ∀ j, InR D j → regular₂ (T.Q.Xo j) T.Q.c (T.U j)

  datum_condition : T.G.PinDat
  tower : T.G.PinTower
  hasData_condition : T.G.HasData
  points_condition : T.G.PinPts
  lattice_condition : T.G.PinLat
  bc66 : T.G.BaseChange

  datIndep : ∀ j, 1 ≤ j → j < D.R.m → DatIndep (T.Q.Xo j) T.Q.c

  nabPin : ∀ j, InR D j → ∃ _ : StarRing (𝓞 D.host.E), IsNab (T.Q.Xo j) T.Q.c (T.nab j)

  nabUniq : ∀ j, InR D j → NabUniq (T.Q.Xo j) T.Q.c

  thTot : ∀ j, InR D j → ThValTot (T.Q.Xo j) T.Q.c (T.nab j)
  thCusp : ∀ j, InR D j → ThInCusp (T.Q.Xo j) T.Q.c (T.nab j) (T.cuspA j)
  thNe : ∀ j, 1 ≤ j → j < D.R.m → ThNe0 (T.Q.Xo j) T.Q.c (T.nab j)

  kPsi : ∀ j, InR D j → KPsiIn (Dw := T.Q.Dw j) T.Q.c

structure LawsSh (T : Top D) : Prop where
  beta : ∀ j, InR D j → ∀ n, BetaExists (Dw := T.Q.Dw j) T.Q.c n (badN D)
  dLev : ∀ j, InR D j → ∀ n, (T.dδ j n).IsLev
  dNab : ∀ j, InR D j → ∀ n, ∃ _ : StarRing (𝓞 D.host.E), IsNab (T.dδ j n).Xo₂ (T.dδ j n).c₂ (T.dδ j n).nab₂

  dPd : ∃ p, (p = D.host.pde ∨ p = D.host.pde') ∧ ∀ j, InR D j → ∀ n, (T.dδ j n).pd = p

  dPhi : ∀ j, InR D j → ∀ n, D.R.r ≤ n → ∃ ph ψ x₀, ψ ≠ 1 ∧ (T.dδ j n).PhiPin ph ψ x₀ ∧ (T.dδ j n).PsiTie ψ

  dRoot : ∀ j, InR D j → ∀ n, ∃ (Cls : Type) (_ : CommGroup Cls) (_ : Finite Cls) (δ : Cls →* (T.dδ j n).c₂.Fˣ)
    (gdet : FrPt (T.dδ j n).Xo₂ (T.dδ j n).c₂ (CAt (T.dδ j n).c₂.F.val.toRingHom) → Cls),
    CMP (T.Q.Xo j) T.Q.c (T.dδ j n) _ Cls δ gdet false
  shTot : ∀ j, InR D j → ∀ a n, Dom a n →
    ShortValTot (T.Q.Xo j) T.Q.c (T.nab j) (badN D) D.R.nV a n (T.dδ j n)
  shCusp : ∀ j, InR D j → ∀ a n, Dom a n → LastPos (T.Q.Dw j) a →
    ShortInCusp (T.Q.Xo j) T.Q.c (T.nab j) (badN D) D.R.nV (T.cuspA j) a n (T.dδ j n)
  shNe : ∀ j, 1 ≤ j → j < D.R.m → ShortNe0 (T.Q.Xo j) T.Q.c (T.nab j) (badN D) D.R.nV (T.dδ j) (T.cuspA j)

def Packet66Rest (Q : Par D) : Prop :=
  ∃ G : In66 Q, G.PinDat ∧ G.PinTower ∧ G.HasData ∧ G.PinPts ∧ G.PinLat ∧ G.BaseChange

end Formalism.L2.Pj
end
end

section

noncomputable section

namespace Formalism.L2.Pj

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Char

variable {D : D7} {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {Comp : Type}

def CUnit (c : Comp → ℂ) : Prop := ∀ k, ‖c k‖ = 1

def muPin (V : HSp D) {X : Comp → Data E r} (dict : GA D V → Σ k, Frame (X k).Ψ r) (mu : GA D V → ℂ)
    (c : Comp → ℂ) : GA D V → ℂ :=
  fun g => c (dict g).1 * mu g

theorem adel_muPin (V : HSp D) {X : Comp → Data E r} (dict : GA D V → Σ k, Frame (X k).Ψ r) (mu : GA D V → ℂ)
    (c : Comp → ℂ) (P : FDSec X) (g : GA D V) :
    adel V dict (muPin V dict mu c) P g = c (dict g).1 * mu g * P (dict g).1 (dict g).2 := rfl

def MuVal (V : HSp D) (χ : (AE D)ˣ →* Circle) (mu : GA D V → ℂ) : Prop :=
  (∀ g, ∃ x, IsDetRoot V g x) ∧ ∀ g x, IsDetRoot V g x → mu g = ((χ x : Circle) : ℂ)

theorem MuVal.norm {V : HSp D} {χ : (AE D)ˣ →* Circle} {mu : GA D V → ℂ} (h : MuVal V χ mu) (g : GA D V) :
    ‖mu g‖ = 1 := by
  obtain ⟨x, hx⟩ := h.1 g
  rw [h.2 g x hx]
  first
    | exact Circle.norm_coe _
    | exact Circle.abs_coe _
    | exact mem_sphere_zero_iff_norm.mp (χ x).2

def FinUnit (x : (AE D)ˣ) : Prop :=
  infPart D (x : AE D) = 1 ∧ finPart D (x : AE D) ∈ intAE D ∧ finPart D ((x⁻¹ : (AE D)ˣ) : AE D) ∈ intAE D

def MuConj {K : Type} [Field K] (σ₀ σ : K →+* ℂ) (χ₀ χσ : (AE D)ˣ →* Circle) : Prop :=
  ∀ x, FinUnit x → ∃ y : K, ((χ₀ x : Circle) : ℂ) = σ₀ y ∧ ((χσ x : Circle) : ℂ) = σ y

def CEquiv (V : HSp D) {K : Type} [Field K] (σ : K →+* ℂ) {C : Type} [AddCommGroup C] [Module K C]
    {X : Comp → Data E r} (rd : C →ₛₗ[σ] FDSec X) (dict : GA D V → Σ k, Frame (X k).Ψ r) (mu : GA D V → ℂ)
    (c : Comp → ℂ) {G0 : Type} [Group G0] (ρ : G0 →* (C →ₗ[K] C)) (chi : G0 →* Kˣ) (ℓ : G0 → GA D V) : Prop :=
  (∃ c' : Comp → ℂ, CUnit c' ∧ EquivariantFiniteGroup V σ rd dict (muPin V dict mu c') ρ chi ℓ) →
    EquivariantFiniteGroup V σ rd dict (muPin V dict mu c) ρ chi ℓ

end Char

section Dict

variable {D : D7}

def finVec (V : HSp D) (v : Fin V.rank → D.host.E) : Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E :=
  fun i => (1 : Af D.host.F) ⊗ₜ v i

def gLat (V : HSp D) (g : GA D V) : Set (Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E) :=
  (finHom V g).1.mulVec '' (latHat V : Set (Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E))

def latG (V : HSp D) (g : GA D V) : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E) :=
  Submodule.span (𝓞 D.host.E) {w | ∃ a : D.host.E, a ∈ D.host.AA ∧ ∃ v, finVec V v ∈ gLat V g ∧ w = a • v}

def latGHat (V : HSp D) (g : GA D V) : AddSubgroup (Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E) :=
  AddSubgroup.closure {w | ∃ a : D.host.E, a ∈ D.host.AA ∧ ∃ z ∈ gLat V g,
    w = fun i => ((1 : Af D.host.F) ⊗ₜ a) * z i}

def LatEmb (V : HSp D) {La : Type} [AddCommGroup La] [Module (𝓞 D.host.E) La]
    (ι : La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)) : Prop :=
  Function.Injective ι ∧ LinearMap.range ι = latG V 1

def LatIsom (V : HSp D) {La : Type} [AddCommGroup La] [Module (𝓞 D.host.E) La] (EF : LinearMap.BilinForm ℤ La)
    (ι : La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)) : Prop :=
  ∃ ε : ℤˣ, ∀ x y, ((EF x y : ℤ) : ℚ) = ((ε : ℤ) : ℚ) *
    Algebra.trace ℚ D.host.E (D.host.xi0 * V.hT (V.frame.equivFun.symm (ι x)) (V.frame.equivFun.symm (ι y)))

def ModelW (V : HSp D) {r : ℕ} (hr : V.rank = r) (X : Data D.host.E r) : Prop :=
  X.Gm = -(Matrix.reindex (finCongr hr) (finCongr hr) V.gram).transpose ∧ X.ξ0 = -D.host.xi0

def IsOrthogonalFrame {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
    (x₀ : (E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ) : Prop :=
  ∀ τ ∈ X.Ψ, gram τ X.Gm (x₀ τ) = Matrix.diagonal fun a : Fin r => ((sgn X.p0 (a : ℕ) : ℝ) : ℂ)

variable {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}
  {σ : c.F →+* ℂ} {r : ℕ}


open Classical in
def DictLat (U : Unf Xo c σ r) (V : HSp D) (hr : V.rank = r) (dict : GA D V → Σ k, Frame (U.X k).Ψ r)
    (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)) {g : ℕ} (e : Fin g ≃ Σ τ : D.host.E →+* ℂ, Fin (Dw.mult τ))
    (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1))
    (ik : U.Comp → Fin F.n) (φ : ∀ k, (F.Di (ik k)).La ≃ₗ[𝓞 D.host.E] (U.X k).Λ)
    (th : ∀ k, (U.X k).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ))
    (x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ) : Prop :=
  ((∀ k a b, (((F.Di (ik k)).EF a b : ℤ) : ℚ) = Algebra.trace ℚ D.host.E
        (-(U.X k).ξ0 * herm (U.X k).Gm (φ k a : Fin r → D.host.E) (φ k b))) ∧
    ∀ k (x : (U.X k).dom), ∃ Pm : (F.Di (ik k)).La →+ (Fin g → ℂ),
      (∀ a j, Pm a j = perFr (U.X k) x.1 (φ k a : Fin r → D.host.E) (relab c σ (e j).1) (e j).2) ∧
      IsPeriod (F.Di (ik k)) (fun j => relab c σ (e j).1) Pm ∧ (U.un k x).x = F.u (ik k) Pm ∧
      ∀ τ (i : Fin (Dw.mult τ)), IsDerivAt0 (fun z => (F.ex (ik k) Pm z).left) (Pi.single (e.symm ⟨τ, i⟩) 1)
        ((U.un k x).u τ i)) ∧
    ∀ h : GA D V, ∃ γ ∈ GQ V,
      ((U.X (dict h).1).Λ : Set (Fin r → D.host.E)) =
        (fun v : Fin V.rank → D.host.E => v ∘ Fin.cast hr.symm) '' (latG V (γ * h) : Set _) ∧
      (∀ a ∈ l.Mb.map (H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) • (⊤ : Submodule (𝓞 D.host.E) Dw.La),
        ∃ w ∈ latGHat V (γ * h),
        finVec V ((φ (dict h).1 (F.t (ik (dict h).1) a) : Fin r → D.host.E) ∘ Fin.cast hr) -
          (finHom V (γ * h)).1.mulVec (finVec V (ι a)) = (l.M : ℕ) • w) ∧
      ∀ τ : (U.X (dict h).1).Ψ, mat (dict h).2 τ =
        Matrix.reindex (finCongr hr) (finCongr hr) (archM V (th (dict h).1 τ) (γ * h)) * x₀ τ.1

end Dict

structure CoreJ (D : D7) : Type 1 extends Core D where
  cE : ∀ (j : ℕ) (σ : Q.c.F →+* ℂ), (U j σ).Comp → ℂ
  chiW : ℕ → (Q.c.F →+* ℂ) → (AE D)ˣ →* Circle
  x₀ : ℕ → (Q.c.F →+* ℂ) → (D.host.E →+* ℂ) → Matrix (Fin D.R.r) (Fin D.R.r) ℂ
  iota : ∀ j : ℕ, (Q.Dw j).La →ₗ[𝓞 D.host.E] (Fin D.R.r → D.host.E)

namespace CoreJ

variable {D : D7} (T : CoreJ D)

def phiJ (j : ℕ) (σ : T.Q.c.F →+* ℂ) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (f : T.R j) : GA D (T.V j σ) → ℂ :=
  (lieFac (T.Q.Dw j) (xiR D) a : ℂ) •
    adel (T.V j σ) (T.dict j σ) (muPin (T.V j σ) (T.dict j σ) (T.mu j σ) (T.cE j σ)) (rdU (T.U j σ) f)

theorem phiJ_apply (j : ℕ) (σ : T.Q.c.F →+* ℂ) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (f : T.R j) (g : GA D (T.V j σ)) :
    T.phiJ j σ a f g = T.cE j σ (T.dict j σ g).1 * T.toCore.phiAd j σ a f g := by
  have h1 : adel (T.V j σ) (T.dict j σ) (T.mu j σ) (rdU (T.U j σ) f) g =
      T.mu j σ g * rdU (T.U j σ) f (T.dict j σ g).1 (T.dict j σ g).2 := rfl
  simp only [phiJ, Core.phiAd, Pi.smul_apply, smul_eq_mul, adel_muPin, h1]
  ring

end CoreJ

def halfVec {D : D7} (V : HSp D) (b : 𝓞 D.host.E) (z : Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E) :
    Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E :=
  fun i => ((1 : Af D.host.F) ⊗ₜ (b : D.host.E)) * z i

def KfHalf {D : D7} (V : HSp D) (Kf : Subgroup (GA D V)) (M : ℕ) (Mh : Ideal (𝓞 D.host.E)) : Prop :=
  ∀ k, k ∈ Kf ↔ k ∈ GfC V ∧ ∀ b ∈ Mh, ∀ z ∈ latHat V, ∃ y ∈ latHat V,
    (finHom V k).1.mulVec (halfVec V b z) - halfVec V b z = M • y

def AdPin {D : D7} (T : Core D) (j : ℕ) (σ : T.Q.c.F →+* ℂ) (x₀ : (D.host.E →+* ℂ) → Matrix (Fin D.R.r) (Fin D.R.r) ℂ)
    (ι₀ : (T.Q.Dw j).La →ₗ[𝓞 D.host.E] (Fin D.R.r → D.host.E)) : Prop :=
  ∃ (hr : (T.V j σ).rank = D.R.r)
    (g : ℕ) (e : Fin g ≃ Σ τ : D.host.E →+* ℂ, Fin ((T.Q.Dw j).mult τ))
    (F : FamilyUnif (T.Q.Xo j) (σ.comp (IntermediateField.inclusion T.Q.c.le).toRingHom)
      (fun i => relab T.Q.c σ (e i).1))
    (ik : (T.U j σ).Comp → Fin F.n) (φ : ∀ k, (F.Di (ik k)).La ≃ₗ[𝓞 D.host.E] ((T.U j σ).X k).Λ)
    (th : ∀ k, ((T.U j σ).X k).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)),
    let ι := LinearMap.funLeft (𝓞 D.host.E) D.host.E (Fin.cast hr) ∘ₗ ι₀
    LatEmb (T.V j σ) ι ∧ LatIsom (T.V j σ) (T.Q.Dw j).EF ι ∧ (∀ k τ, Formalism.MainNotions.StandardLattice.IsInfEmb τ.1 (th k τ)) ∧
      DictLat (T.U j σ) (T.V j σ) hr (T.dict j σ) ι e F ik φ th x₀

structure LawsJ {D : D7} (T : CoreJ D) : Prop extends LawsM T.toCore where

  cUnit : ∀ j, InR D j → ∀ σ, GoodEmb T.Q.c σ → CUnit (T.cE j σ)

  muVal : ∀ j, InR D j → ∀ σ, GoodEmb T.Q.c σ → MuVal (T.V j σ) (T.chiW j σ) (T.mu j σ)

  muConj : ∀ j, InR D j → ∀ σ, GoodEmb T.Q.c σ → MuConj T.σ₀ σ (T.chiW j T.σ₀) (T.chiW j σ)

  intAll : ∀ j, InR D j → IntAll (T.Q.Xo j) T.Q.c

  modelW : ∀ j, InR D j → ∀ σ, GoodEmb T.Q.c σ → ∃ hr : (T.V j σ).rank = D.R.r,
    ∀ k, ModelW (T.V j σ) hr ((T.U j σ).X k)

  familyUniformisationBasePointOrthogonal : ∀ j, InR D j → ∀ σ, GoodEmb T.Q.c σ → ∀ k, IsOrthogonalFrame ((T.U j σ).X k) (T.x₀ j σ)

  kfHalf : ∀ j, InR D j → ∀ σ, GoodEmb T.Q.c σ →
    KfHalf (T.V j σ) (T.Kf j σ) T.Q.l.M (T.Q.l.Mb.map (T.Q.H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E))

  adPin : ∀ j, InR D j → ∀ σ, GoodEmb T.Q.c σ → AdPin T.toCore j σ (T.x₀ j σ) (T.iota j)

end Formalism.L2.Pj
end
end

section

noncomputable section

-- Prefer the same-scalar submodule instance for the cuspidal spaces.
attribute [local instance 2000] Submodule.module

namespace Formalism.L2.Pj

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions

variable {D : D7} (T : Core D)

namespace Core

abbrev C (j : ℕ) (w : WeightFamilies.Wt D j) : Submodule T.Q.c.F (T.R j) := T.cuspA j (wtA w) w.n

abbrev Vs (j : ℕ) (la : HeightOneSpectrum (𝓞 T.Q.c.F)) : Set (T.R j → EReal) :=
  valSet (T.Q.Xo j) T.Q.c (algCls (T.Q.Xo j) T.Q.c) la

def Ns (j : ℕ) (w : WeightFamilies.Wt D j) (σ : T.Q.c.F →+* ℂ) : T.R j → ℝ :=
  supC (T.Q.Xo j) T.Q.c (T.U j) (xiR D) (goodOf T.Q.c σ) (wtA w) w.n

def Cu (j : ℕ) : Type := {_cu : FJ.CuF (T.X₀ j) (WeightFamilies.rho D j) // InR D j}

def Xc (j : ℕ) (cu : T.Cu j) : Submodule (𝓞 D.host.E) (Fin (WeightFamilies.rho D j) → D.host.E) :=
  FJ.XcF (T.X₀ j) T.frI cu.1

theorem Xc_lat (j : ℕ) (cu : T.Cu j) : Submodule.IsLattice D.host.E (T.Xc j cu) :=
  FJ.xcLatF (T.X₀ j) T.frI one_ne_zero cu.1

abbrev FJt (j : ℕ) (cu : T.Cu j) (_χ : WeightFamilies.ExpoSet D (T.Xc j cu)) (_w : WeightFamilies.Wt D j) : Type :=
  FJ.FJtF T.σ₀ (T.X₀ j) cu.1

end Core

variable {T} (h : LawsCore T)

namespace LawsCore


open Classical in
def Nl (j : ℕ) (w : WeightFamilies.Wt D j) (σ : T.Q.c.F →+* ℂ) : T.R j → ℝ :=
  if hj : InR D j then
    l2C (T.U j) (goodOf T.Q.c σ) (T.V j _) (T.dict j _) (T.mu j _) (xiR D) (wtA w) w.n
      (h.cuspidalL2Subspace j hj _ (goodEmb_goodOf _ σ) _ _ (dom_wtA w))
  else 0

def sg (j : ℕ) (cu : T.Cu j) (χ : WeightFamilies.ExpoSet D (T.Xc j cu)) (w : WeightFamilies.Wt D j) :
    T.C j w →ₗ[T.Q.c.F] T.FJt j cu χ w :=
  FJ.sgF T.σ₀ (T.X₀ j) (rdC (T.U j) T.σ₀ (wtA w) w.n)
    (FJ.rdOrbInt_of_latZ T.σ₀ (T.X₀ j) _ (rdC_continuousOn (h.unf j cu.2 T.σ₀ T.good_σ₀) (dom_wtA w)) (h.latZ j cu.2))
    cu.1 χ.1

include h

theorem fd (j : ℕ) (hj : InR D j) (w : WeightFamilies.Wt D j) : FiniteDimensional T.Q.c.F (T.C j w) := by
  exact h.cuspFD j hj (wtA w) w.n (dom_wtA w)

theorem hNs (j : ℕ) (hj : InR D j) (w : WeightFamilies.Wt D j) (σ : T.Q.c.F →+* ℂ) : IsNormOn (T.C j w) σ (T.Ns j w σ) := by
  apply IsNormOn.of_goodOf
  unfold Core.Ns
  have hσ := goodEmb_goodOf T.Q.c σ
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro f _
    exact mul_nonneg (lieFac_pos _ _ _).le (supN_nonneg _ _ _)
  · intro f hf h0
    exact h.supDef j hj _ _ (dom_wtA w) _ hσ f hf
      ((mul_eq_zero.mp h0).resolve_left (lieFac_pos _ _ _).ne')
  · intro a f _
    unfold supC supN
    rw [map_smulₛₗ, supE_smul, ENNReal.toReal_mul, ENNReal.toReal_ofReal (norm_nonneg _)]
    ring
  · intro f hf g hg
    unfold supC supN
    rw [← mul_add, map_add (f := _), ← ENNReal.toReal_add (supE_cusp_ne_top hσ hf) (supE_cusp_ne_top hσ hg)]
    refine mul_le_mul_of_nonneg_left (ENNReal.toReal_mono ?_ (supE_add_le _ _ _ _)) (lieFac_pos _ _ _).le
    exact ENNReal.add_ne_top.mpr ⟨supE_cusp_ne_top hσ hf, supE_cusp_ne_top hσ hg⟩

theorem hNl (j : ℕ) (hj : InR D j) (w : WeightFamilies.Wt D j) (σ : T.Q.c.F →+* ℂ) : IsNormOn (T.C j w) σ (h.Nl j w σ) := by
  rw [Nl, dite_eq_left hj]
  apply IsNormOn.of_goodOf
  let σ' := goodOf T.Q.c σ
  let rd := rdC (T.U j) σ' (wtA w) w.n
  have hσ : GoodEmb T.Q.c σ' := goodEmb_goodOf T.Q.c σ
  have hmem := h.cuspidalL2Subspace j hj σ' hσ (wtA w) w.n (dom_wtA w)
  have hdef := h.l2Def j hj σ' hσ (wtA w) w.n (dom_wtA w)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro f hf
    rw [l2C, dite_eq_left hf]
    exact mul_nonneg (lieFac_pos _ _ _).le
      (l2Norm_nonneg_bis (T.V j σ') σ' rd (T.dict j σ') (T.mu j σ') hmem ⟨f, hf⟩)
  · intro f hf h0
    rw [l2C, dite_eq_left hf] at h0
    exact congrArg Subtype.val (hdef ⟨f, hf⟩ ((mul_eq_zero.mp h0).resolve_left (lieFac_pos _ _ _).ne'))
  · intro a f hf
    rw [l2C, l2C, dite_eq_left hf, dite_eq_left (Submodule.smul_mem _ a hf)]
    have hsmul := l2Norm_smul_alt (T.V j σ') σ' rd (T.dict j σ') (T.mu j σ') hmem a ⟨f, hf⟩
    exact (congrArg (lieFac (T.Q.Dw j) (xiR D) (wtA w) * ·) hsmul).trans (by ac_rfl)
  · intro f hf g hg
    rw [l2C, l2C, l2C, dite_eq_left hf, dite_eq_left hg, dite_eq_left (Submodule.add_mem _ hf hg), ← mul_add]
    exact mul_le_mul_of_nonneg_left
      (L2Norm_add_le (T.V j σ') σ' rd (T.dict j σ') (T.mu j σ') hmem ⟨f, hf⟩ ⟨g, hg⟩)
      (lieFac_pos _ _ _).le

theorem hle (j : ℕ) (hj : InR D j) (w : WeightFamilies.Wt D j) (σ : T.Q.c.F →+* ℂ) :
    ∀ f ∈ T.C j w, h.Nl j w σ f ≤ T.Ns j w σ f := by
  rw [Nl, dite_eq_left hj]
  obtain ⟨_, _, _, hD⟩ := h.dictU j hj _ (goodEmb_goodOf _ σ)
  exact l2C_le_supC _ (goodEmb_goodOf _ σ) _ hD.2.2.2.1 (h.muUnit j hj _ (goodEmb_goodOf _ σ))

theorem mul (j : ℕ) (hj : InR D j) (w w' : WeightFamilies.Wt D j) :
    ∀ f ∈ T.C j w, ∀ g ∈ T.C j w', f * g ∈ T.C j (WeightAlgebra.wadd w w') := by
  intro f hf g hg
  have e := h.cuspMul j hj (wtA w) (wtA w') w.n w'.n f g (dom_wtA w) (dom_wtA w') hf hg
  have e1 : f * g = mulC (T.Q.Xo j) T.Q.c f g := rfl
  have e2 : (WeightAlgebra.wadd w w').n = w.n + w'.n := rfl
  have e3 : wtA (WeightAlgebra.wadd w w') = wtA w + wtA w' := by
    clear e e1 e2 hf hg f g h
    funext x
    simp only [wtA, WeightAlgebra.wadd, Pi.add_apply]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun t _ => ?_)
    have e4 : ∀ {p : ℕ} (a b : Fin p → ℕ) k, ext0 (fun i => a i + b i) k = ext0 a k + ext0 b k := by
      intro p a b k
      unfold ext0
      split_ifs <;> simp
    simp only [e4]
    split_ifs <;> omega
  show f * g ∈ cusp (T.Q.Xo j) T.Q.c (T.U j) (wtA (WeightAlgebra.wadd w w')) (WeightAlgebra.wadd w w').n
  rw [e1, e2, e3]
  exact e

end LawsCore

abbrev recB : WeightFamilies.Prov D :=
  mkB T.Q.eO T.C h.fd T.Vs (fun _ la => isVal_valSet la) T.Ns h.Nl h.hNs h.hNl h.hle T.Cu T.Xc T.Xc_lat T.FJt h.sg

end Formalism.L2.Pj
end
end

section

noncomputable section

namespace Formalism.L2.Pj

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions

variable {D : D7}

structure LawsPi (T : Core D) (Dd : DepData D.host.E) : Prop where

  page : Dd.Q.g1 = D.host.g 0 ∧ Dd.Q.g2 = D.host.g 1 ∧ Dd.Q.q1 = D.host.q ∧ Dd.Q.dd = D.host.d ∧ Dd.Q.f = D.R.f ∧
    Dd.Q.r = D.R.r
  tPos : TPos Dd

  sm : Dd.Q.sm = D.host.small

  wts : ∀ j, InR D j → (∀ τ, Antitone fun i => Dd.aL j (τ, i)) ∧ 2 * D.R.f * D.R.r ≤ Dd.nW j

  piSplit : PiSplit (H := T.Q.H) Dd
  piHalf : PiHalf T.Q.l Dd

structure LawsDep (T : Core D) [StarRing (𝓞 D.host.E)] : Prop where

  star_eq : ∀ a : 𝓞 D.host.E, star a = T.Q.H.bar a

  chartEx : ∀ j, InR D j → IntChartEx (T.Q.Xo j) T.Q.c
  chartIndep : ∀ j, InR D j → ChartIndep (T.Q.Xo j) T.Q.c

def NuFinAt (T : Core D) (Dd : DepData D.host.E) [StarRing (𝓞 D.host.E)] : Prop :=
  ∀ j, InR D j → ∀ la : HeightOneSpectrum (𝓞 T.Q.c.F), nuWAt (Xo := T.Q.Xo j) Dd la j ≠ ⊤

end Formalism.L2.Pj
end
end
