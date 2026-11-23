module

public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceAdeleRing
public import Development.AbelianVarietyTheory.Definitions.Foundations.GLintEqKOAndPrincEqKOne
public import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.GraphHeightLattice

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.Doubling
open Formalism.UG (GLint)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

def IsElemDiv {v : HeightOneSpectrum (𝓞 F)} (x : GL (Fin n) (Fv F v)) (d : Fin n → (Fv F v)ˣ) : Prop :=
  ∃ k₁ ∈ GLint (Fin n) (v.adicCompletionIntegers F).toSubring,
    ∃ k₂ ∈ GLint (Fin n) (v.adicCompletionIntegers F).toSubring,
      x.1 = k₁.1 * Matrix.diagonal (fun i => (d i : Fv F v)) * k₂.1

def IsInertUnder (v : HeightOneSpectrum (𝓞 F)) (P : HeightOneSpectrum (𝓞 E)) : Prop :=
  v.asIdeal.map (algebraMap (𝓞 F) (𝓞 E)) = P.asIdeal

variable (σ : E →ₐ[F] E) (J : Matrix (Fin n) (Fin n) E) (L : Submodule (𝓞 E) (Fin n → E))
  (v : HeightOneSpectrum (𝓞 F))

def latMoved (g : GLoc σ J v) : Submodule (intLoc F E v) (Fin n → Fv F v ⊗[F] E) :=
  (latLoc F L v).comap ((Matrix.mulVecLin (matHom (Fv F v) σ J g⁻¹).1).restrictScalars (intLoc F E v))

def latLength (g : GLoc σ J v) : ℕ∞ :=
  Module.length (intLoc F E v)
    (latLoc F L v ⧸ (latLoc F L v ⊓ latMoved σ J L v g).submoduleOf (latLoc F L v))

def graphHgt (g : GLoc σ J v) : ℝ≥0 :=
  hgtFin σ (dblGram finSumFinEquiv J) L v (ioH (Fv F v) σ rfl (g, 1))

def SplitAt (h : IsCMExt F E σ) (hJ : IsHermND σ J) : Prop :=
  ∀ (τ : E →ₐ[F] Fv F v) (β : GL (Fin n) (Fv F v)), IsSplitBasis τ L β → ∀ g : GLoc σ J v,
    (∃ d, IsElemDiv (splitEquivIn h hJ τ β g) d) ∧
    (∀ d, IsElemDiv (splitEquivIn h hJ τ β g) d →
      graphHgt σ J L v g = ∏ i, min ‖(d i : Fv F v)‖₊ ‖(d i : Fv F v)‖₊⁻¹) ∧
    graphHgt σ J L v g ≤ 1

def InertAt : Prop :=
  ∀ P : HeightOneSpectrum (𝓞 E), IsInertUnder v P → ∀ g : GLoc σ J v,
    (∃ l : ℕ, latLength σ J L v g = l ∧
      graphHgt σ J L v g = ((Ideal.absNorm P.asIdeal : ℕ) : ℝ≥0) ^ (-(l : ℤ))) ∧
    graphHgt σ J L v g ≤ 1

def GraphNormFinite : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (h : IsCMExt F E σ) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (hJ : IsHermND σ J)
    (L : Submodule (𝓞 E) (Fin n → E)) [Submodule.IsFullLattice E L] (v : HeightOneSpectrum (𝓞 F)),
    IsSelfDualAt σ J L v → SplitAt σ J L v h hJ ∧ InertAt σ J L v

omit [NumberField E] in
theorem mem_latMoved {g : GLoc σ J v} {x : Fin n → Fv F v ⊗[F] E} :
    x ∈ latMoved σ J L v g ↔ (matHom (Fv F v) σ J g⁻¹).1 *ᵥ x ∈ latLoc F L v := Iff.rfl


end GlobalTheory.IndefiniteRowSideFullHecke.GraphHeightLattice

end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links NumberField

namespace GlobalTheory.IndefiniteRowSideFullHecke.RationalFormValues

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

abbrev lamV (D : D7) (i : Fin D.R.m) : D.what₂.Tau → DomWeight (Vc D i).rank :=
  fun τ => Bridge.lamLdef (Vc D i).rank ((i : ℕ) + 1) τ

def IsCoefExt {K K' : Type} [Field K] [Field K'] {σ : K →+* ℂ} {σ' : K' →+* ℂ} (ι : K →+* K')
    {I : Type} [Fintype I] {n : ℕ} (lam : I → DomWeight n) {W : Type} [AddCommGroup W] [Module ℂ W]
    (c₀ : VV K lam →ₛₗ[σ] W) (c' : VV K' lam →ₛₗ[σ'] W) : Prop :=
  ∀ (v : VV K lam) (v' : VV K' lam), (v' : Pol K' I n) = MvPolynomial.map ι (v : Pol K I n) → c' v' = c₀ v

section Row

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

def formFn (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (x : A.fam.amb.FL i t) : Bridge.Gf (Vc D i) → (R.cV i).W :=
  (R.HV i t).e (R.jV i t x)

def ValuesIn (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) {K' : Type} [Field K'] {σ' : K' →+* ℂ}
    (c' : VV K' (lamV D i) →ₛₗ[σ'] (R.cV i).W) : Prop :=
  ∀ (x : A.fam.amb.FL i t) (h : Bridge.Gf (Vc D i)), ∃ v : VV K' (lamV D i), c' v = formFn R i t x h

def RationalValuesAt (R : RealDat D A Ks) : Prop :=
  ∀ (gramR : Matrix (Fin D.sp.X'.rank) (Fin D.sp.X'.rank) D.host.E)
    (c0R : VV D.what₂.LL (fun τ => Bridge.lamRdef (Ptw D) τ) →ₛₗ[D.what₂.embLL] R.cX.coef.W)
    (c0L : ∀ i : Fin D.R.m, VV D.what₂.LL (lamV D i) →ₛₗ[D.what₂.embLL] (R.cV i).coef.W),
    Bridge.FamTie R.B R.pl (R.Sb : Set (Pl D.host.E)) R.Q (labLL D) (fun τ => Bridge.lamRdef (Ptw D) τ) (lamV D) gramR c0R c0L →
    ∀ (i : Fin D.R.m) (t : T) (K' : Type) [Field K'] (ι : D.what₂.LL →+* K') (σ' : K' →+* ℂ), σ'.comp ι = D.what₂.embLL →
      ∀ c' : VV K' (lamV D i) →ₛₗ[σ'] (R.cV i).W, IsCoefExt (W := (R.cV i).W) ι (lamV D i) (c0L i) c' → ValuesIn R i t c'

end Row

def RationalValues : Prop :=
  ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m)
    (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A),
    R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsFam → R.IsModels → RationalValuesAt R

end GlobalTheory.IndefiniteRowSideFullHecke.RationalFormValues

end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links
open scoped TensorProduct

namespace GlobalTheory.IndefiniteRowSideFullHecke.SublevelSplitting

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

abbrev Lat (V : HSp D) : Type := Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)

def matF (V : HSp D) (h : Bridge.Gf V) :
    Matrix (Fin V.rank) (Fin V.rank) (Af D.host.F ⊗[D.host.F] D.host.E) :=
  Units.val (h : GL (Fin V.rank) (Af D.host.F ⊗[D.host.F] D.host.E))

def compAtPl (V : HSp D) (v : HeightOneSpectrum (𝓞 D.host.F)) (h : Bridge.Gf V) :
    Matrix (Fin V.rank) (Fin V.rank) (Fv D.host.F v ⊗[D.host.F] D.host.E) :=
  (matF V h).map (Algebra.TensorProduct.map (evalV D.host.F v) (AlgHom.id D.host.F D.host.E))


variable (D) in
def IsSplitPl (v : HeightOneSpectrum (𝓞 D.host.F)) : Prop :=
  ∃ P P' : HeightOneSpectrum (𝓞 D.host.E), P ≠ P' ∧ P.under (𝓞 D.host.F) = v ∧ P'.under (𝓞 D.host.F) = v

def SuppSplitOff (V : HSp D) (bad : ℕ) (h : Bridge.Gf V) : Prop :=
  ∃ Sp : Finset (HeightOneSpectrum (𝓞 D.host.F)),
    (∀ v ∈ Sp, IsSplitPl D v ∧ (bad : 𝓞 D.host.F) ∉ v.asIdeal) ∧ ∀ v, v ∉ Sp → compAtPl V v h = 1

def IsTransl (V : HSp D) (Λ : Lat V) (h : Bridge.Gf V) (L : Lat V) : Prop :=
  ∀ x : Fin V.rank → D.host.E, x ∈ L ↔
    (matF V h⁻¹).mulVec (fun i => (1 : Af D.host.F) ⊗ₜ[D.host.F] x i) ∈
      latHat D.host.F D.host.E (Λ : Set (Fin V.rank → D.host.E))

def IsOpenLev (V : HSp D) (J' : Subgroup (Bridge.Gf V)) : Prop :=
  IsOpen ((J'.comap (finHom V).rangeRestrict : Subgroup (GA D V)) : Set (GA D V))

def IsSubLev (V : HSp D) (J J' : Subgroup (Bridge.Gf V)) (vol : ℝ) : Prop :=
  J' ≤ J ∧ J'.relIndex J ≠ 0 ∧ IsOpenLev V J' ∧ vol = ((J'.relIndex J : ℕ) : ℝ)⁻¹

def IsAdReps (V : HSp D) (Λ : Lat V) (J' : Subgroup (Bridge.Gf V)) (bad : ℕ) {n : ℕ} (h : Fin n → Bridge.Gf V)
    (Lh : Fin n → Lat V) (gam : Fin n → ℕ) : Prop :=
  Bridge.IsReps (Bridge.ratF V) J' h ∧ (∀ a, SuppSplitOff V bad (h a)) ∧ (∀ a, IsTransl V Λ (h a) (Lh a)) ∧
    ∀ a, Finite (Bridge.stab (Bridge.ratF V) J' (h a)) ∧ gam a = Nat.card (Bridge.stab (Bridge.ratF V) J' (h a))

def IsLatReps (V : HSp D) (Λ : Lat V) (bad : ℕ) {n : ℕ} (Lh : Fin n → Lat V) : Prop :=
  (∀ a, Submodule.IsLattice D.host.E (Lh a) ∧ Formalism.L2.Herm.dualL D.sp.cm V (Lh a) = Lh a ∧
    ∃ M : ℕ, 0 < M ∧ M.Coprime bad ∧ (∀ x ∈ Λ, (M : D.host.E) • x ∈ Lh a) ∧ ∀ x ∈ Lh a, (M : D.host.E) • x ∈ Λ) ∧
  ∀ (g : Bridge.Gf V) (L : Lat V), IsTransl V Λ g L →
    ∃ (a : Fin n) (γ : GL (Fin V.rank) D.host.E), γ ∈ UR D.sp.cm V.gram ∧
      ∀ x, x ∈ Lh a ↔ (γ : Matrix (Fin V.rank) (Fin V.rank) D.host.E).mulVec x ∈ L

variable {T : Type}

def levJ (L : LevCh D T) (i : Fin D.R.m) (t : T) : Subgroup (Bridge.Gf (Vc D i)) :=
  (levEnv (Vc D i) (L.βV i) (L.datVt i t)).J

def IsBad (L : LevCh D T) (t : T) (bad : ℕ) : Prop :=
  0 < bad ∧ ∀ PP : Pl D.host.E, PP ∈ L.Pg ∨ PP ∈ L.Q t → (bad : 𝓞 D.host.E) ∈ PP.asIdeal

def RepsAt (L : LevCh D T) (i : Fin D.R.m) (t : T) (N : ℕ) : Prop :=
  ∃ (n : ℕ) (h : Fin n → Bridge.Gf (Vc D i)) (J' : Subgroup (Bridge.Gf (Vc D i))) (bad : ℕ) (Lh : Fin n → Lat (Vc D i))
    (gam : Fin n → ℕ) (vol : ℝ),
    IsBad L t bad ∧ N ∣ bad ∧ IsSubLev (Vc D i) (levJ L i t) J' vol ∧
      IsAdReps (Vc D i) (L.ΛV i) J' bad h Lh gam ∧ IsLatReps (Vc D i) (L.ΛV i) bad Lh

section Row

variable {G : Type} [Group G] [Fintype G] {Pl0 : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

def RowAt (R : RealDat D A Ks) : Prop :=
  R.toLevCh.Is A.μ0 → RealDat.models_vpos (D := D) →
    ∀ (i : Fin D.R.m) (t : T) (N : ℕ), 0 < N → RepsAt R.toLevCh i t N

end Row

def Row : Prop :=
  ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m)
    (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), RowAt R

end GlobalTheory.IndefiniteRowSideFullHecke.SublevelSplitting

end
end
