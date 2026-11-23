module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle009
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle010
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EqOfPowEqOneOfNormSubLt
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.Bundle004
public import Formalism.LocalRingCardinality.DataIdx
public import Formalism.LocalToGlobal.Columns.AlgebraMapMemMaximalIdealPowIff
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Formalism.ConjugateSelfDual.Bundle001
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.BlochKatoPhases
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import ReciprocityTheory.GaloisValuations.GlobalA

@[expose] public section

section

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen
open scoped ENNReal TensorProduct

namespace GlobalTheory.TwSys.Test

section Ord
variable (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

end Ord

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N}



end GlobalTheory.TwSys.Test

end
end

section

noncomputable section
namespace GlobalTheory.Present
open scoped LaurentSeries PowerSeries
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n₀ : ℕ}
    (W : LocWach PD LL O v n₀) {k : Type} [Field k] [Algebra O k]

def DΔ (T : LocLat G Qp LL O) : AddSubgroup (W.DD T) where
  carrier := {x | ∀ δ ∈ W.DelF, W.γD T δ x = x}
  zero_mem' := fun δ _ => map_zero _
  add_mem' := fun ha hb δ hδ => by rw [map_add (f := _), ha δ hδ, hb δ hδ]
  neg_mem' := fun ha δ hδ => by rw [map_neg, ha δ hδ]

def Onto (T : LocLat G Qp LL O) (A : Ob k G) (q : ↥T.L.T →ₗ[O] (Fin A.m → k)) : Prop :=
  Function.Surjective q ∧ ∀ σ x, q (latRep T.L σ x) = A.ρ σ (q x)

structure Pres {l n : ℕ} {R : RingPG k l} (F : DFun R n G) (ι : k⸨X⸩ →ₐ[k] k⸨X⸩) (τ : ZMod n → ZMod n₀)
    (γ : W.Gam) where
  ι_v : ι (vv k) = ((PowerSeries.map (algebraMap O k) W.π₀₁ : k⟦X⟧) : k⸨X⸩)
  obj : ∀ (T : LocLat G Qp LL O) (A : Ob k G) q, Onto T A q → F.Obj A

  j : ∀ (T : LocLat G Qp LL O) (A : Ob k G), (↥T.L.T →ₗ[O] (Fin A.m → k)) → ZMod n → (↥(DΔ W T) →+ Vc k A.m)
  j_surj : ∀ T A q, Onto T A q → ∀ i, Function.Surjective (j T A q i)
  j_smul : ∀ T A q, Onto T A q → ∀ i (a : LetA O n₀) (c : k⟦X⟧) (x y : ↥(DΔ W T)),
    ι (c : k⸨X⸩) = ((PowerSeries.map (algebraMap O k) (a (τ i)) : k⟦X⟧) : k⸨X⸩) →
    (y : W.DD T) = a • (x : W.DD T) → j T A q i y = c • j T A q i x
  j_φ : ∀ T A q, Onto T A q → ∀ i (x y : ↥(DΔ W T)), (y : W.DD T) = W.φD T x →
    j T A q i y = (F.D A).φ i (j T A q (i - 1) x)
  j_γ : ∀ T A q, Onto T A q → ∀ i (x y : ↥(DΔ W T)), (y : W.DD T) = W.γD T γ x →
    j T A q i y = (F.D A).γ i (j T A q i x)
  j_ker : ∀ T A q, Onto T A q → ∀ (T' : LocLat G Qp LL O) (f : LatHom T'.L T.L), Function.Injective f.f →
    (∀ x : ↥T.L.T, q x = 0 ↔ ∃ y ∈ T'.L.T, f.f y = x) → ∀ i (x : ↥(DΔ W T)),
    j T A q i x = 0 ↔ ∃ y, W.map f y = (letE (τ i) : LetA O n₀) • (x : W.DD T)
  j_map : ∀ T A q T' A' q', Onto T A q → Onto T' A' q' → ∀ (f : LatHom T.L T'.L)
    (g : (Fin A.m → k) →ₗ[k] (Fin A'.m → k)), IsHom A A' g →
    (∀ (x : ↥T.L.T) (x' : ↥T'.L.T), (x' : T'.V) = f.f x → q' x' = g (q x)) →
    ∀ i (x : ↥(DΔ W T)) (y : ↥(DΔ W T')), (y : W.DD T') = W.map f x → j T' A' q' i y = F.map A A' g i (j T A q i x)
  j_unit : ∀ q, Onto W.one (chr 1 : Ob k G) q → ∀ x : ↥(DΔ W W.one),
    W.N W.one = Submodule.span (LetA O n₀) {(x : W.DD W.one)} → ∀ i,
    Submodule.span k⟦X⟧ {j W.one (chr 1) q i x} = Submodule.span k⟦X⟧ {F.unit i}

end GlobalTheory.Present

namespace GlobalTheory.TopSteps.TopSit
open scoped LaurentSeries PowerSeries
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.PhiGam GlobalTheory.Models GlobalTheory.Present
variable {l : ℕ} [Fact l.Prime] {P : LocPrime l} (S : TopSit P)

abbrev W (H : LocHW l P) := H.W S.K 1 S.LL S.hyp.1.2.1.2.2

def RealD (H : LocHW l P) : Prop :=
  ∀ (k : Type) [Field k] [Algebra S.O k] [CharP k l], S.IsRes k →
    ∃ (R : RingPG k l) (ι : k⸨X⸩ →ₐ[k] k⸨X⸩), GlobalTheory.IndefiniteRowSideFullHecke.OnePlusPowerCharacters.IsCyclotomic R ι ∧
    ∃ (F : DFun R S.n S.G) (τ : ZMod S.n → ZMod (Module.finrank ℚ_[l] ↥(K0 S.K))) (γ : (S.W H).Gam),
      (∀ i, (S.W H).emb (τ i) = S.emb i) ∧ ((S.W H).χΓ γ : S.O) = 1 + (l : S.O) ∧
      Nonempty (Pres (S.W H) F ι τ γ)

end GlobalTheory.TopSteps.TopSit
end
end

section

noncomputable section

namespace GlobalTheory.Cut.Check

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal

section Mat
variable {O : Type} [CommRing O] [IsDomain O] {k : ℕ}

theorem matKO_mk (A : Matrix (Fin k) (Fin k) O) (v : Fin k → FractionRing O) :
    matKO A (Submodule.Quotient.mk v) =
      Submodule.Quotient.mk ((A.map (algebraMap O (FractionRing O))).mulVec v) := rfl

theorem matKO_smul_one (a : O) (x : KOG O k) :
    matKO (a • (1 : Matrix (Fin k) (Fin k) O)) x = a • x := by
  induction x using Submodule.Quotient.induction_on with
  | H v =>
    rw [matKO_mk, ← Submodule.Quotient.mk_smul]
    congr 1
    funext j
    have : ∀ x, (a • (1 : Matrix (Fin k) (Fin k) O)) j x = if j = x then a else 0 := fun x => by
      simp [Matrix.one_apply]
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, this, Pi.smul_apply]
    simp [apply_ite, Algebra.smul_def]

theorem WKG_eq_matKO {Γ : Type} [Group Γ] (M : Γ →* Matrix (Fin k) (Fin k) O) (g : Γ) (x : KOG O k) :
    WKG M g x = matKO (M g) x := by
  induction x using Submodule.Quotient.induction_on with
  | H v => rfl
end Mat

variable {D : D7} (i : D.nd.Loc)

variable (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (S : IdempotentChoiceData D.nd i) (Xs : Set (D.nd.X i))

theorem inR'_one : InR' D.nd r S 1 :=
  ⟨1, fun _ => 1, fun _ => 1, fun _ => one_mem _, by funext x; simp⟩

theorem inY_yg (γ : GE D.nd) : InY D.nd r S (yg D.nd r S γ) :=
  ⟨1, fun _ => 1, fun _ => γ, fun _ => inR'_one i r S, by simp⟩

theorem cocW_quad {k : ℕ} (ψ : (S.X' → MatN D.nd i) → Matrix (Fin k) (Fin k) (D.nd.O i)) {v} (hq : QuadAt i r Xs v)
    {c : GE D.nd → KOG (D.nd.O i) k} (hc : c ∈ cocW i r S Xs ψ) (γ) (hγ : γ ∈ Ine (F := D.host.E) (D.nd.plOm.1 v)) :
    matKO (ψ fun x' => rO D.nd i r (S.p x') γ) (c γ) = c γ := by
  induction hc using Submodule.span_induction with
  | mem c hc =>
    obtain ⟨φ, h1, h0, rfl⟩ := hc
    have hg : InR' D.nd r S fun x' => rO D.nd i r (S.p x') γ :=
      ⟨1, fun _ => 1, fun _ => γ, fun _ => one_mem _, by funext x; simp⟩
    have hn : InR' D.nd r S (-1) :=
      ⟨1, fun _ => -1, fun _ => 1, fun _ => neg_mem (one_mem _), by funext x; simp⟩
    have hY : InY D.nd r S ((fun x' => rO D.nd i r (S.p x') γ) * yg D.nd r S γ - yg D.nd r S γ) :=
      ⟨2, ![fun x' => rO D.nd i r (S.p x') γ, -1], fun _ => γ,
        fun j => by fin_cases j; exacts [hg, hn], by simp [Fin.sum_univ_two, sub_eq_add_neg]⟩
    have := h0 _ hY fun x' hx => by
      have hq' := hq _ hx γ hγ
      have e : ((fun x' => rO D.nd i r (S.p x') γ) * yg D.nd r S γ - yg D.nd r S γ) x' =
          (((chiU D.nd i 1 γ)⁻¹ : (D.nd.O i)ˣ) : D.nd.O i) • (((rO D.nd i r (S.p x') γ - 1) *
            (rO D.nd i r (S.p x') γ - ((chiU D.nd i 1 γ : (D.nd.O i)ˣ) : D.nd.O i) • (1 : MatN D.nd i))) *
              Eel D.nd S x') := by
        simp only [yg, Pi.sub_apply, Pi.mul_apply, mul_sub, sub_mul, smul_sub, Matrix.mul_smul, Matrix.smul_mul,
          smul_smul, Units.inv_mul, one_smul, mul_assoc, one_mul, mul_one]
        abel
      rw [e, hq']; simp
    rw [map_sub, sub_eq_zero, h1 _ hg _ (inY_yg i r S γ)] at this
    exact this
  | zero => simp
  | add a b _ _ ha hb => simp only [Pi.add_apply, ha, hb, map_add (f := _)]
  | smul a b _ hb => simp only [Pi.smul_apply, hb, map_smul]

end GlobalTheory.Cut.Check

end
end

section

noncomputable section

namespace GlobalTheory.Cut

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal

variable {D : D7} (i : D.nd.Loc)




def lenCob {k : ℕ} (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i))
    (C : Submodule (D.nd.O i) (GE D.nd → KOG (D.nd.O i) k)) : ℕ∞ :=
  Module.length (D.nd.O i) ↥(C ⊓ (ReciprocityTheory.Gal.B1 (WKG M) : Submodule (D.nd.O i) (GE D.nd → KOG (D.nd.O i) k)))


set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 2000000 in
def InCut (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (Xs : Set (D.nd.X i)) {k : ℕ}
    (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)) (w : HeightOneSpectrum (𝓞 D.host.E))
    (hw : w ∈ placesOver D.host.E (D.nd.l i)) (f : GE D.nd → KOG (D.nd.O i) k) : Prop :=
  locFun i M w hw f ∈ Submodule.span (Br.OLL D.nbr i w hw) (GlobalTheory.Pass.cutCoc i w hw r Xs M)

end GlobalTheory.Cut

end
end

section

noncomputable section

namespace GlobalTheory.GLp

open Polynomial GlobalTheory.GLq
open scoped Classical

variable (g : ℕ) [Fact g.Prime]

def inc (n : ℕ) : GL (Fin n) ℤ_[g] →* GL (Fin n) ℚ_[g] :=
  Matrix.GeneralLinearGroup.map (algebraMap ℤ_[g] ℚ_[g])

def red (n : ℕ) : GL (Fin n) ℤ_[g] →* Gn g n := Matrix.GeneralLinearGroup.map (PadicInt.toZMod (p := g))

def lift (n : ℕ) (x : Gn g n) : GL (Fin n) ℚ_[g] := inc g n (Function.invFun (red g n) x)

variable {g} {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]

def fixK1 (π : Representation ℂ (GL (Fin n) ℚ_[g]) V) : Submodule ℂ V :=
  ⨅ k : (red g n).ker, LinearMap.ker (π (inc g n k) - LinearMap.id)

def actK (π : Representation ℂ (GL (Fin n) ℚ_[g]) V) (a : MonoidAlgebra ℂ (Gn g n)) : V →ₗ[ℂ] V :=
  ∑ x : Gn g n, a.coeff x • π (lift g n x)

def IsIrrRep {G : Type} [Group G] (π : Representation ℂ G V) : Prop :=
  Nontrivial V ∧ ∀ W : Submodule ℂ V, (∀ x, ∀ v ∈ W, π x v ∈ W) → W = ⊥ ∨ W = ⊤

def blk (a b n : ℕ) (x : Gn g a) (y : Gn g b) : Gn g n :=
  toG (fun i j : Fin n =>
    if (i : ℕ) < a ∧ (j : ℕ) < a then Formalism.MainNotions.ArithmeticCylinders.entN (x : Mt g a) i j
    else if a ≤ (i : ℕ) ∧ a ≤ (j : ℕ) then Formalism.MainNotions.ArithmeticCylinders.entN (y : Mt g b) (i - a) (j - a) else 0)

def IsParVec (π : Representation ℂ (GL (Fin n) ℚ_[g]) V) (a b : ℕ) (χ : (ZMod g)ˣ →* ℂˣ) (v : V) : Prop :=
  v ∈ fixK1 π ∧
    (∀ u : Gn g n, InPar a (u : Mt g n) → tl a (u : Mt g n) = 1 → br a b (u : Mt g n) = 1 → π (lift g n u) v = v) ∧
    ∀ y : Gn g b, π (lift g n (blk a b n 1 y)) v = ((χ (Matrix.GeneralLinearGroup.det y) : ℂˣ) : ℂ) • v

def actTop (π : Representation ℂ (GL (Fin n) ℚ_[g]) V) (a b : ℕ) (e : MonoidAlgebra ℂ (Gn g a)) : V →ₗ[ℂ] V :=
  ∑ x : Gn g a, e.coeff x • π (lift g n (blk a b n x 1))

def IsCharLab (L : LabelDatum g) (χ : (ZMod g)ˣ →* ℂˣ) (c : ZMod g) : Prop :=
  c ≠ 0 ∧ ∀ u : (ZMod g)ˣ, algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g) u = L.gen 1 →
    ((χ u : ℂˣ) : ℂ) = L.teich (algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g) c)

end GlobalTheory.GLp
end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst TensorProduct
open scoped Formalism.Per

namespace GlobalTheory.PMon

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l)

def Fil (a : ℤ) : Set P.R.BdR := ((P.PD (botExt l)).Fil a : Set P.R.BdR)

def fr (l : ℕ) [Fact l.Prime] (m : ℕ) : ↥(MaximalUnramifiedExtension l) →+* ↥(MaximalUnramifiedExtension l) := ((frobUr l ^ m : ↥(MaximalUnramifiedExtension l) →ₐ[ℚ_[l]] ↥(MaximalUnramifiedExtension l)) : ↥(MaximalUnramifiedExtension l) →+* ↥(MaximalUnramifiedExtension l))

def kd : ↥(MaximalUnramifiedExtension l) →+* P.R.BdR := (algebraMap (Om l) P.R.BdR).comp (algebraMap ↥(MaximalUnramifiedExtension l) (Om l))

def ks : ↥(MaximalUnramifiedExtension l) →+* Bst P := (Polynomial.C : P.R.B →+* Bst P).comp (algebraMap ↥(MaximalUnramifiedExtension l) P.R.B)

def ev (m : ℕ) (b : P.R.B) : P.R.BdR := P.ιB (P.φB^[m] b)

def tz (a : ℤ) : P.R.BdR := P.ιB (((isUnit_tB P).unit ^ a : P.R.Bˣ) : P.R.B)

variable {n : Type} [Fintype n] [DecidableEq n]

def UnitM (U : GL n P.R.BdR) : Prop :=
  (∀ i j, (U : Matrix n n P.R.BdR) i j ∈ Fil P 0) ∧ ∀ i j, ((U⁻¹ : GL n P.R.BdR) : Matrix n n P.R.BdR) i j ∈ Fil P 0

variable {K : FinExt l}

structure IsRat (r : ℕ) (ρ : ↥(GK K) →* GL n ↥(MaximalUnramifiedExtension l)) : Prop where

  pos : 0 < r

  le : ∀ c : ↥(MaximalUnramifiedExtension l), fr l r c = c → (c : Om l) ∈ K.1

  rat : ∀ g i j, fr l r ((ρ g : Matrix n n ↥(MaximalUnramifiedExtension l)) i j) = (ρ g : Matrix n n ↥(MaximalUnramifiedExtension l)) i j

  cont : ∀ i j, Continuous fun g => (((ρ g : Matrix n n ↥(MaximalUnramifiedExtension l)) i j : ↥(MaximalUnramifiedExtension l)) : Om l)

def matD (ρ : ↥(GK K) →* GL n ↥(MaximalUnramifiedExtension l)) (m : ℕ) (g : ↥(GK K)) : Matrix n n P.R.BdR :=
  (ρ g : Matrix n n ↥(MaximalUnramifiedExtension l)).map fun c => kd P (fr l m c)

def AdmDR (ρ : ↥(GK K) →* GL n ↥(MaximalUnramifiedExtension l)) : Prop :=
  ∀ m : ℕ, ∃ Q : GL n P.R.BdR, ∀ g : ↥(GK K),
    matD P ρ m g * (Q : Matrix n n P.R.BdR).map (P.actQdR (g : GQ l)) = Q

def Framed {r : ℕ} (ρ : ↥(GK K) →* GL n ↥(MaximalUnramifiedExtension l)) (w : Fin r → n → ℤ) : Prop :=
  ∀ m : Fin r, ∃ U : GL n P.R.BdR, UnitM P U ∧ ∀ g : ↥(GK K),
    matD P ρ m g * (U : Matrix n n P.R.BdR).map (P.actQdR (g : GQ l)) =
      (U : Matrix n n P.R.BdR) * Matrix.diagonal fun j =>
        algebraMap ℚ_[l] P.R.BdR ((P.χQ (g : GQ l) ^ w m j : ℚ_[l]ˣ) : ℚ_[l])

def AdmSt (ρ : ↥(GK K) →* GL n ↥(MaximalUnramifiedExtension l)) : Prop :=
  ∃ (K' : FinExt l) (hK : K.1 ≤ K'.1) (Q : GL n (Bst P)), ∀ g : ↥(GK K'),
    (ρ ⟨g, GK_le hK g.2⟩ : Matrix n n ↥(MaximalUnramifiedExtension l)).map (ks P) *
      (Q : Matrix n n (Bst P)).map (actSt P (g : GQ l)) = Q

def Splits (r : ℕ) (ρ : ↥(GK K) →* GL n ↥(MaximalUnramifiedExtension l)) : Prop :=
  ∃ (s : Finset n) (p : GL n ↥(MaximalUnramifiedExtension l)), s.Nonempty ∧ s ≠ Finset.univ ∧
    (∀ i j, fr l r ((p : Matrix n n ↥(MaximalUnramifiedExtension l)) i j) = (p : Matrix n n ↥(MaximalUnramifiedExtension l)) i j) ∧
    ∀ g i j, i ∉ s → j ∈ s → ((p⁻¹ * ρ g * p : GL n ↥(MaximalUnramifiedExtension l)) : Matrix n n ↥(MaximalUnramifiedExtension l)) i j = 0

def eps {α : Type} [DecidableEq α] (x y z : α) : ℤ := if z = x then -1 else if z = y then 1 else 0


variable {P} in
def Plus {AI : LocAinf l P} (T : LocTied l P AI) (b : P.R.B) : Prop :=
  ∃ (N : ℕ) (x : Formalism.Per.Acris l), T.eB ((l : P.R.B) ^ N * b) = algebraMap (Formalism.Per.Acris l) (Formalism.Per.Bcris l) x

end GlobalTheory.PMon

end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain

namespace GlobalTheory.EtaJoin

variable (D : D7)

def ratSub (μ : D.what₂.Tup) (j : ℕ) (U : Submodule ℂ (D.what₂.Mt μ j)) : Submodule D.what₂.LL (D.what₂.MtL μ j) :=
  U.comap (D.what₂.jMt μ j)

def genSet (μ : D.what₂.Tup) (j : ℕ) : Set (D.what₂.MtL μ j) :=
  {x | D.what₂.jMt μ j x ∈ (D.what₂.MtLat μ j).gen}

def lat (μ : D.what₂.Tup) (j : ℕ) : Submodule (𝓞 D.what₂.LL) (D.what₂.MtL μ j) :=
  Submodule.span (𝓞 D.what₂.LL) (genSet D μ j)

def up (μ : D.what₂.Tup) (j : ℕ) : Submodule (𝓞 D.what₂.LL) (D.what₂.MtL μ j) :=
  (ratSub D μ j (Idx.Z0 D μ j)).restrictScalars (𝓞 D.what₂.LL) ⊓
    (lat D μ j ⊔ (ratSub D μ j (Idx.Z0 D μ j)ᗮ).restrictScalars (𝓞 D.what₂.LL))

def low (μ : D.what₂.Tup) (j : ℕ) : Submodule (𝓞 D.what₂.LL) (D.what₂.MtL μ j) :=
  lat D μ j ⊓ (ratSub D μ j (Idx.Z0 D μ j)).restrictScalars (𝓞 D.what₂.LL)

def etaRat (μ : D.what₂.Tup) (j : ℕ) (w : D.what₂.places.Pl) : ℚ :=
  Formalism.L2.Col.lenUW (D.plEq w) (up D μ j) (low D μ j)

def ZRat (μ : D.what₂.Tup) (j : ℕ) : Prop :=
  ratSub D μ j (Idx.Z0 D μ j) ⊔ ratSub D μ j (Idx.Z0 D μ j)ᗮ = ⊤

def SpecPr (i : D.nd.Loc) : Prop :=
  (∀ y ∈ ratSub D (D.nd.mu i) (D.nd.j i) (Idx.Z0 D (D.nd.mu i) (D.nd.j i)),
    D.nd.prMt i y ∈ D.nd.eigSum i (↑(D.nd.Zgood i))) ∧
  (∀ y ∈ ratSub D (D.nd.mu i) (D.nd.j i) (Idx.Z0 D (D.nd.mu i) (D.nd.j i))ᗮ,
    D.nd.prMt i y ∈ D.nd.eigSum i (↑(D.nd.Zgood i))ᶜ)

def ZSpec (i : D.nd.Loc) : Prop :=
  ∀ P : D.naut.AV i,
    (D.naut.typeV i P ≤ Idx.Z0 D (D.nd.mu i) (D.nd.j i) ∨ D.naut.typeV i P ≤ (Idx.Z0 D (D.nd.mu i) (D.nd.j i))ᗮ) ∧
    ∀ x, D.naut.ptV i P = some x →
      (x ∈ D.nd.Zgood i → D.naut.typeV i P ≤ Idx.Z0 D (D.nd.mu i) (D.nd.j i)) ∧
      (x ∉ D.nd.Zgood i → D.naut.typeV i P ≤ (Idx.Z0 D (D.nd.mu i) (D.nd.j i))ᗮ)

def TypeTie (i : D.nd.Loc) : Prop :=
  ∀ (S : Set (D.naut.AV i)) (y : D.what₂.MtL (D.nd.mu i) (D.nd.j i)),
    D.what₂.jMt (D.nd.mu i) (D.nd.j i) y ∈ (⨆ P ∈ S, D.naut.typeV i P) →
    D.nd.prMt i y ∈ D.nd.eigSum i {x | ∃ P ∈ S, D.naut.ptV i P = some x}

def TypeOrth (i : D.nd.Loc) : Prop :=
  ∀ P P' : D.naut.AV i, P ≠ P' → D.naut.typeV i P ⟂ D.naut.typeV i P'

def ThetaCut (μ : D.what₂.Tup) (j : ℕ) : Prop :=
  D.what₂.Zj μ j ≤ LinearMap.range (D.what₂.eMt μ j)

def SplitUnif : Prop :=
  ∀ v : PlE D.host, IsSplitPl D.host v → ∃ (s : SplitPlace D.host.E)
    (ϖ : s.v.adicCompletion (maximalRealSubfield D.host.E)), IsConjPl D.host v s.w ∧ IsUnif D.host.E s.v ϖ

variable {D}

def HeckeScalar (M : MtFam D) (i : D.nd.Loc) : Prop :=
  ∀ (P : D.naut.AV i) (w : PlE D.host) (k : ℕ) (s : SplitPlace D.host.E)
    (ϖ : s.v.adicCompletion (maximalRealSubfield D.host.E)), SplitOut D.nd i w → IsConjPl D.host w s.w →
    IsUnif D.host.E s.v ϖ → 1 ≤ k → k ≤ D.R.nV → ∃ c : ℂ, ∀ y ∈ D.naut.typeV i P,
    NG.tN (M.loc i).J s ϖ k ((M.loc i).real y) = c • (M.loc i).real y

def latLoc {M : MtFam D} (B : NLocBase D M) (j : ℕ) (w : D.what₂.places.Pl) : Submodule (B.Oc j w) (B.V j w) :=
  Submodule.span (B.Oc j w) (B.iV j w '' genSet D (D.what₂.muTw w) j)

def LatStable {M : MtFam D} (B : NLocBase D M) (j : ℕ) (w : D.what₂.places.Pl) : Prop :=
  ∀ v k, GenAt D (D.what₂.places.resChar w) (B.Qc j w) v k → ∀ x ∈ latLoc B j w, B.hK j w v k x ∈ latLoc B j w

end GlobalTheory.EtaJoin
end
end
