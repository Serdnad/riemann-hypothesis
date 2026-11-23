module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle008
public import Formalism.LocalToGlobal.ProjectiveLattices.RulInst
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistedModelAdmissibleCocycles
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle001
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle006
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle006
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
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Topology.Sheaves.Init
import Mathlib.Tactic.ReduceModChar
import ReciprocityTheory.BasicDefinitions.ExistsUnique

@[expose] public section

section

noncomputable section

namespace GlobalTheory.Cut

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal

def matKO {O : Type} [CommRing O] [IsDomain O] {k : ℕ} (A : Matrix (Fin k) (Fin k) O) :
    KOG O k →ₗ[O] KOG O k :=
  (stdG O (FractionRing O) k).mapQ (stdG O (FractionRing O) k)
    (((A.map (algebraMap O (FractionRing O))).mulVecLin).restrictScalars O) (by
      rintro _ ⟨u, rfl⟩
      refine ⟨A.mulVec u, ?_⟩
      funext j
      exact RingHom.map_mulVec (algebraMap O (FractionRing O)) A u j)

variable {D : D7} (i : D.nd.Loc)

def ccOff (Xs : Set (D.nd.X i)) (π : D.nd.X i) : Ideal (D.nd.O i) :=
  Ideal.span {a | ∃ f ∈ D.nd.T i, (∀ x ∈ Xs, x ∉ D.nd.Z i → f x = 0) ∧ a = f π}

def vccOff (Xs : Set (D.nd.X i)) (π : D.nd.X i) : ℚ :=
  lenUnit (O := D.nd.O i) (D.nd.l i) (D.nd.O i ⧸ ccOff i Xs π)

def lenQ (a : D.nd.O i) : ℕ∞ := Module.length (D.nd.O i) (D.nd.O i ⧸ Ideal.span {a})

variable (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (S : IdempotentChoiceData D.nd i) (Xs : Set (D.nd.X i))

def cocW {k : ℕ} (ψ : (S.X' → MatN D.nd i) → Matrix (Fin k) (Fin k) (D.nd.O i)) :
    Submodule (D.nd.O i) (GE D.nd → KOG (D.nd.O i) k) :=
  Submodule.span (D.nd.O i)
    {c | ∃ φ : (S.X' → MatN D.nd i) →ₗ[D.nd.O i] KOG (D.nd.O i) k,
      (∀ a, InR' D.nd r S a → ∀ y, InY D.nd r S y → φ (a * y) = matKO (ψ a) (φ y)) ∧
      (∀ y, InY D.nd r S y → (∀ x', S.p x' ∈ Xs → y x' = 0) → φ y = 0) ∧
      c = fun γ => φ (yg D.nd r S γ)}

def cocRho : Submodule (D.nd.O i) (GE D.nd → KOG (D.nd.O i) D.R.r) := cocW i r S Xs S.ψρ

def cocChi (c : Fin D.R.t) : Submodule (D.nd.O i) (GE D.nd → KOG (D.nd.O i) 1) :=
  cocW i r S Xs fun a => S.ψχ c a • (1 : Matrix (Fin 1) (Fin 1) (D.nd.O i))

def locFun {k : ℕ} (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)) (w : HeightOneSpectrum (𝓞 D.host.E))
    (hw : w ∈ placesOver D.host.E (D.nd.l i)) (c : GE D.nd → KOG (D.nd.O i) k) :
    Br.G D.nbr i w hw → (Fin k → Br.LL D.nbr i w hw) ⧸ (Br.locLat D.nbr i w hw M).T :=
  fun g => Br.phi (D.nbr i w hw) k (c ((Br.iota D.nbr i w hw g : Gw D.nd w) : GE D.nd))

def IsFinL {k : ℕ} (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)) (c : GE D.nd → KOG (D.nd.O i) k) : Prop :=
  ∀ w hw, locFun i M w hw c ∈ HfD (Br.PD D.loc D.nbr i w hw) (Br.locLat D.nbr i w hw M)

def resIne {k : ℕ} (C : Submodule (D.nd.O i) (GE D.nd → KOG (D.nd.O i) k)) (v : HeightOneSpectrum (𝓞 D.host.E)) :
    Submodule (D.nd.O i) (↥(Ine (F := D.host.E) (D.nd.plOm.1 v)) → KOG (D.nd.O i) k) :=
  C.map (LinearMap.funLeft (D.nd.O i) (KOG (D.nd.O i) k) Subtype.val)

def QuadAt (v : HeightOneSpectrum (𝓞 D.host.E)) : Prop :=
  ∀ x ∈ Xs, ∀ γ ∈ Ine (F := D.host.E) (D.nd.plOm.1 v),
    (rO D.nd i r x γ - 1) *
      (rO D.nd i r x γ - ((chiU D.nd i 1 γ : (D.nd.O i)ˣ) : D.nd.O i) • (1 : MatN D.nd i)) = 0

def PolyAt (π : D.nd.X i) (v : HeightOneSpectrum (𝓞 D.host.E)) : Prop :=
  ∃ P : Polynomial (D.nd.T i),
    (∀ x ∈ Xs, ∀ γ ∈ Ine (F := D.host.E) (D.nd.plOm.1 v),
      Polynomial.aeval (rO D.nd i r x (D.nd.gam0 i v)) (P.map (evT D.nd i x)) *
        (rO D.nd i r x γ - ((chiU D.nd i 1 γ : (D.nd.O i)ˣ) : D.nd.O i) • (1 : MatN D.nd i)) = 0) ∧
    IsUnit ((P.map (evT D.nd i π)).eval (D.nd.zeta i v))

def NoChiOff : Prop :=
  ∀ x ∈ Xs, x ∉ D.nd.Z i → ∀ u : Fin D.R.nV → KK D.nd i,
    (∀ g, (mapM (toK D.nd i) (rTwO D.nd i r x) g).mulVec u = u) → u = 0

def UnrOut : Prop :=
  ∀ v, v ∉ placesOver D.host.E (D.nd.l i) → v ∉ D.nd.S i → v ∉ D.nd.Q i →
    ∀ x ∈ Xs, ∀ γ ∈ Ine (F := D.host.E) (D.nd.plOm.1 v), rTwO D.nd i r x γ = 1

def GlobalCore : Prop :=
  ∀ (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (Xs : Set (D.nd.X i)) (eρ eχ : ℕ)
    (S : IdempotentChoiceData D.nd i),
    GoodR D.nd i r → GoodCongruenceObjects D.nd r ρ π S → π ∈ D.nd.Z i → π ∈ Xs →
    NoChiOff i r Xs → UnrOut i r Xs →
    (∀ v ∈ D.nd.S i, (QuadAt i r Xs v ∧ IsUnit (D.nd.zeta i v - 1)) ∨ PolyAt i r Xs π v) →
    (∀ v ∈ D.nd.Q i, QuadAt i r Xs v ∧ D.nd.zeta i v ≠ 1) →
    (∀ w (hw : w ∈ placesOver D.host.E (D.nd.l i)), GlobalTheory.Pass.HfChar i w hw ∧
      GlobalTheory.Pass.LocBound i w hw r Xs (WpO D.nd i ρ π) eρ ∧
      ∀ c ∈ Finset.Icc 1 D.R.t, GlobalTheory.Pass.LocBound i w hw r Xs (chiRatO D.nd i c) eχ) →
    Br.sFin D.loc D.nbr i ρ π →
    (∀ e ∈ Finset.Ioo 0 D.R.t, Formalism.GaloisCohomology.shaLen (D.nd.ldat (D.nd.l i)) (e : ℤ) < ⊤) →
    vccOff i Xs π ≤
      (((placesOver D.host.E (D.nd.l i)).ncard * (eρ + D.R.t * eχ) : ℕ) : ℚ) +
      Br.sPi D.loc D.nbr i ρ π + (∑ e ∈ Finset.Ioo 0 D.R.t, (D.what₂.shaLen (D.nd.l i) e : ℚ)) +
      (padicValNat (D.nd.l i) (hE D.host) : ℚ) + 4 * (D.R.nV : ℚ) * D.nd.vdel i +
      (D.R.t : ℚ) * ∑ q ∈ D.nd.Q i,
        lenUnit (O := D.nd.O i) (D.nd.l i) (D.nd.O i ⧸ Ideal.span {D.nd.zeta i q - 1})

end GlobalTheory.Cut

end
end

section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.GoodPtsModel

open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.GoodPts

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l}

theorem inV_iff_val (T : CDVR) (x : T.Fr) : InV T x ↔ valV T.V x ≤ 1 := by
  constructor
  · rintro ⟨a, rfl⟩
    exact HeightOneSpectrum.valuation_le_one _ a
  · intro h
    exact IsDiscreteValuationRing.exists_lift_of_le_one h

theorem inV_iff_vV (T : CDVR) {x : T.Fr} (hx : x ≠ 0) : InV T x ↔ 0 ≤ vV T.V x := by
  have h0 : valV T.V x ≠ 0 := (valV T.V).ne_zero_iff.mpr hx
  rw [inV_iff_val, vV, neg_nonneg, WithZero.log_le_iff_le_exp h0, WithZero.exp_zero]

theorem inV_iff_nval (T : CDVR) {e : ℕ} (he : 0 < e) (x : T.Fr) : InV T x ↔ 0 ≤ nval T.V e x := by
  unfold nval
  by_cases hx : x = 0
  · subst hx
    rw [if_pos rfl]
    exact iff_of_true (algebraMap T.V T.Fr).range.zero_mem le_top
  · rw [if_neg hx, inV_iff_vV T hx, EReal.coe_nonneg, le_div_iff₀ (by exact_mod_cast he), zero_mul,
      Int.cast_nonneg_iff]

variable {la : HeightOneSpectrum (𝓞 c.F)}

theorem bddAll_iff_smul (κ : c.F) (f : Rul Xo c) : BddAll Xo c la κ f ↔ BddAll Xo c la 1 (κ • f) := by
  unfold BddAll
  simp only [map_one, one_mul, evI_smul]

private theorem evI_add_non_galois_descent {T : CDVR} {io : c.F →+* T.Fr} (y : IntFr Xo c T io) (f g : Rul Xo c) :
    evI y (f + g) = evI y f + evI y g := by
  letI := io.toAlgebra
  exact evalAt_add _ _ f g _

theorem bddAll_add {κ : c.F} {f g : Rul Xo c} (hf : BddAll Xo c la κ f) (hg : BddAll Xo c la κ g) :
    BddAll Xo c la κ (f + g) := by
  intro T io e ho y hy
  rw [evI_add_non_galois_descent, mul_add]
  exact (algebraMap T.V T.Fr).range.add_mem (hf T io e ho y hy) (hg T io e ho y hy)

theorem inV_io {T : CDVR} {io : c.F →+* T.Fr} {e : ℕ} (ho : OverLa la T.V io e) {a : c.F} (ha : a ≠ 0) :
    InV T (io a) ↔ 0 ≤ vLa la a := by
  obtain ⟨he, hv⟩ := ho
  rw [inV_iff_vV T ((map_ne_zero io).mpr ha), hv a]
  exact mul_nonneg_iff_of_pos_left (by exact_mod_cast he)

theorem smul_mem_supSet {W : Submodule c.F (Rul Xo c)} {a : c.F} (ha : 0 ≤ vLa la a) {f : Rul Xo c}
    (hf : f ∈ supSet Xo c la W) : a • f ∈ supSet Xo c la W := by
  obtain ⟨hW, hb⟩ := hf
  show a • f ∈ W ∧ BddAll Xo c la 1 (a • f)
  refine ⟨W.smul_mem a hW, ?_⟩
  intro T io e ho y hy
  have h1 := hb T io e ho y hy
  rw [map_one, one_mul] at h1
  rw [map_one, one_mul, evI_smul]
  have h2 : InV T (io a) := by
    by_cases ha0 : a = 0
    · rw [ha0, map_zero]
      exact (algebraMap T.V T.Fr).range.zero_mem
    · exact (inV_io ho ha0).mpr ha
  exact (algebraMap T.V T.Fr).range.mul_mem h2 h1

private theorem vV_mul' (T : CDVR) {a b : T.Fr} (ha : a ≠ 0) (hb : b ≠ 0) :
    vV T.V (a * b) = vV T.V a + vV T.V b := by
  rw [vV, vV, vV, map_mul, WithZero.log_mul ((valV T.V).ne_zero_iff.mpr ha)
    ((valV T.V).ne_zero_iff.mpr hb), neg_add]

private theorem inV_mul_iff_vLa_add_nval_nonneg {T : CDVR} {io : c.F →+* T.Fr} {e : ℕ} (ho : OverLa la T.V io e)
    {κ : c.F} (hκ : κ ≠ 0) (z : T.Fr) :
    InV T (io κ * z) ↔ 0 ≤ (((vLa la κ : ℤ) : ℝ) : EReal) + nval T.V e z := by
  obtain ⟨he, hv⟩ := ho
  have hk : io κ ≠ 0 := (map_ne_zero io).mpr hκ
  by_cases hz : z = 0
  · subst hz
    rw [mul_zero]
    unfold nval
    rw [if_pos rfl, EReal.coe_add_top]
    exact iff_of_true (algebraMap T.V T.Fr).range.zero_mem le_top
  · have he' : (0 : ℝ) < e := by exact_mod_cast he
    rw [inV_iff_vV T (mul_ne_zero hk hz), vV_mul' T hk hz, hv κ, nval, if_neg hz,
      ← EReal.coe_add, EReal.coe_nonneg,
      show ((vLa la κ : ℤ) : ℝ) + (vV T.V z : ℝ) / e = (((e : ℤ) * vLa la κ + vV T.V z : ℤ) : ℝ) / e by
        push_cast; field_simp,
      le_div_iff₀ he', zero_mul, Int.cast_nonneg_iff]

theorem bddAll_iff_vAtV {κ : c.F} (hκ : κ ≠ 0) (f : Rul Xo c) :
    BddAll Xo c la κ f ↔
      ∀ y : PtV Xo c (fun _ _ y => y.IsAlg) Unit (fun _ _ _ _ => True) la,
        0 ≤ (((vLa la κ : ℤ) : ℝ) : EReal) + vAtV y f := by
  constructor
  · rintro h ⟨q, T, io, e, ho, y, hy, eta, -, rfl⟩
    exact (inV_mul_iff_vLa_add_nval_nonneg ho hκ _).mp (h T io e ho y hy)
  · intro h T io e ho y hy
    exact (inV_mul_iff_vLa_add_nval_nonneg ho hκ _).mpr (h (Subtype.mk _ ⟨T, io, e, ho, y, hy, (), trivial, rfl⟩))

end GlobalTheory.GoodPtsModel
end
end

section

noncomputable section
namespace GlobalTheory.TopSteps
open scoped LaurentSeries PowerSeries TensorProduct
open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc
open Formalism.MainNotions.N (twistRep coefRep)
open ReciprocityTheory.Def (Z1 H1 H2)

def Repr {k G : Type} [Field k] [Group G] {l n : ℕ} {R : RingPG k l} (F : DFun R n G) (A : Ob k G)
    (z : G → Fin A.m → k) (b g : ZMod n → Vc k A.m) : Prop :=
  ∃ (E : Ob k G) (a : (Fin A.m → k) →ₗ[k] (Fin E.m → k)) (p : (Fin E.m → k) →ₗ[k] (Fin 1 → k)) (e : Fin E.m → k)
    (ε : ZMod n → Vc k E.m), F.Obj E ∧ IsHom A E a ∧ IsHom E (chr 1) p ∧ Function.Injective a ∧
    Function.Exact a p ∧ p e = (fun _ => 1) ∧ (∀ σ, E.ρ σ e = e + a (z σ)) ∧
    ∀ i, F.map E (chr 1) p i (ε i) = F.unit i ∧
      F.map A E a i (b i) = (F.D E).φ i (ε (i - 1)) - ε i ∧ F.map A E a i (g i) = (F.D E).γ i (ε i) - ε i

def KerIs {O M N : Type} [CommRing O] [AddCommGroup M] [Module O M] [AddCommGroup N] [Module O N] (lam : O)
    (q : M →ₗ[O] N) : Prop := ∀ x, q x = 0 ↔ ∃ y, x = lam • y

def IndepMod {O M : Type} [CommRing O] [AddCommGroup M] [Module O M] (lam : O) {s : ℕ} (c : Fin s → M) : Prop :=
  ∀ x : Fin s → O, ∑ a, x a • c a = 0 → ∀ a, lam ∣ x a

variable {l : ℕ} [Fact l.Prime]

structure TopSit (P : LocPrime l) where
  K : FinExt l
  LL : FinExt l
  n : ℕ
  r : ℕ
  [nz : NeZero n]
  emb : ZMod n → (↥(K0 K) →ₐ[ℚ_[l]] ↥LL.1)
  D : TopData n r
  Γ : GalData ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)
  hyp : GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleTwistedCharClasses.Hyp P K LL emb D Γ

attribute [instance] TopSit.nz

namespace TopSit
variable {P : LocPrime l} (S : TopSit P)

abbrev O : Type := ↥(OL S.LL)

abbrev G : Type := ↥(GK S.K)

abbrev admitted {M : Type} [AddCommGroup M] [Module S.O M] (π : Representation S.O S.G M) : Prop :=
  Admissible (P.PD S.K) S.emb S.Γ S.D.t S.D.Ut π

abbrev cls {M : Type} [AddCommGroup M] [Module S.O M] (W : Representation S.O S.G M) (X : Type) [AddCommGroup X]
    [Module S.O X] : Set (H1 (twCoef W S.Γ.χ₁ X) ⊤) := adm (P.PD S.K) S.emb S.Γ S.D.t S.D.Ut W X

def IsRes (k : Type) [Field k] [Algebra S.O k] : Prop :=
  Function.Surjective (algebraMap S.O k) ∧ ∀ x, algebraMap S.O k x = 0 ↔ S.Γ.lam ∣ x

def Real : Prop :=
  ∀ (k : Type) [Field k] [Algebra S.O k] [CharP k l], S.IsRes k →
    ∃ (R : RingPG k l) (ι : k⸨X⸩ →ₐ[k] k⸨X⸩), GlobalTheory.IndefiniteRowSideFullHecke.OnePlusPowerCharacters.IsCyclotomic R ι ∧
    ∃ (F : DFun R S.n S.G) (M : ModTh F S.D), (∀ σ, (M.ω σ : k) = algebraMap S.O k (S.Γ.ε σ)) ∧
      (∃ q : ↥S.Γ.T₀.L.T →ₗ[S.O] (Fin M.T.m → k), Function.Surjective q ∧
        KerIs S.Γ.lam q ∧ ∀ σ x, q (twistRep S.Γ.W₀ S.Γ.χ₁⁻¹ σ x) = M.T.ρ σ (q x)) ∧
      ∀ (A : Ob k S.G) (N : Type) [AddCommGroup N] [Module S.O N] (π : Representation S.O S.G N)
        (e : N ≃ₗ[S.O] (Fin A.m → k)), S.admitted π → (∀ σ x, e (twistRep π S.Γ.χ₁⁻¹ σ x) = A.ρ σ (e x)) →
        ∃ L, M.Model A L

def Closed : Prop :=
  ∀ (M M' : Type) [AddCommGroup M] [Module S.O M] [AddCommGroup M'] [Module S.O M']
    (π : Representation S.O S.G M) (π' : Representation S.O S.G M'),
    (∀ f : M →ₗ[S.O] M', (∀ σ x, f (π σ x) = π' σ (f x)) →
      (Function.Injective f → S.admitted π' → S.admitted π) ∧ (Function.Surjective f → S.admitted π → S.admitted π')) ∧
    (S.admitted π → S.admitted π' → S.admitted (π.prod π'))

def CoefAdm {M : Type} [AddCommGroup M] [Module S.O M] (W : Representation S.O S.G M) : Prop :=
  ∀ (X : Type) [AddCommGroup X] [Module S.O X] [Finite X], S.admitted (coefRep W X)

def StdAdm : Prop := S.CoefAdm S.Γ.W₀ ∧ ∀ c : ℕ, 1 ≤ c → c ≤ S.D.t → S.CoefAdm (S.Γ.Wchi c)

def Lem0 {M : Type} [AddCommGroup M] [Module S.O M] (W : Representation S.O S.G M) : Prop :=
  ∀ (X : Type) [AddCommGroup X] [Module S.O X] [Finite X],
    (∃ A : Submodule S.O (H1 (twCoef W S.Γ.χ₁ X) ⊤), S.cls W X = A) ∧
    (∀ (a : ℕ) (ha : ∀ x : X, S.Γ.lam ^ a • x = 0), 1 ≤ a →
      S.cls W X = admAt (P.PD S.K) S.emb S.Γ S.D.t S.D.Ut W X a ha) ∧
    ∀ (X' : Type) [AddCommGroup X'] [Module S.O X'] [Finite X'] (f : X →ₗ[S.O] X') (c : H1 (twCoef W S.Γ.χ₁ X) ⊤),
      (c ∈ S.cls W X → coefH1 W S.Γ.χ₁ f c ∈ S.cls W X') ∧
      (Function.Injective f → coefH1 W S.Γ.χ₁ f c ∈ S.cls W X' → c ∈ S.cls W X)

def ResBound {M : Type} [AddCommGroup M] [Module S.O M] (W : Representation S.O S.G M) (s₀ : ℕ) : Prop :=
  ∀ (s : ℕ) (c : Fin s → H1 (twCoef W S.Γ.χ₁ (GlobalTheory.IndefiniteRowSideFullHecke.InvariantsVanishing.resK S.Γ)) ⊤),
    (∀ a, c a ∈ S.cls W (GlobalTheory.IndefiniteRowSideFullHecke.InvariantsVanishing.resK S.Γ)) →
    IndepMod S.Γ.lam c → s ≤ s₀

def Vanish : Prop :=
  (GlobalTheory.IndefiniteRowSideFullHecke.InvariantsVanishing.resRep S.Γ).invariants = ⊥ ∧ Subsingleton (H2 (GlobalTheory.IndefiniteRowSideFullHecke.InvariantsVanishing.resRep S.Γ) ⊤)

def FreeH : Prop :=
  (Module.Free S.O (GlobalTheory.IndefiniteRowSideFullHecke.InvariantsVanishing.HH S.Γ) ∧ Module.Finite S.O (GlobalTheory.IndefiniteRowSideFullHecke.InvariantsVanishing.HH S.Γ) ∧
    Module.finrank S.O (GlobalTheory.IndefiniteRowSideFullHecke.InvariantsVanishing.HH S.Γ) = S.r * S.n) ∧
  ∀ (X : Type) [AddCommGroup X] [Module S.O X] [Finite X], TensIso S.Γ.T₀.L S.Γ.χ₁ X

def FSummand : Prop :=
  (∃ C : Submodule S.O (GlobalTheory.IndefiniteRowSideFullHecke.InvariantsVanishing.HH S.Γ), IsCompl (GlobalTheory.IndefiniteRowSideFullHecke.InvariantsVanishing.Hf (P.PD S.K) S.Γ) C) ∧
    Module.finrank S.O ↥(GlobalTheory.IndefiniteRowSideFullHecke.InvariantsVanishing.Hf (P.PD S.K) S.Γ) = S.D.dsum

def FinAdm : Prop :=
  ∀ (X : Type) [AddCommGroup X] [Module S.O X] [Finite X],
    (finiteSelmer (P.PD S.K) S.Γ.T₀.L S.Γ.χ₁ X : Set _) ⊆ S.cls S.Γ.W₀ X

def UnrAdm : Prop :=
  ∀ (X : Type) [AddCommGroup X] [Module S.O X] [Finite X],
    GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleCharUnramified.homModInertia S.Γ X (IK S.K) ⊆ S.cls (S.Γ.Wchi 1) X

def CrysCalc : Prop :=
  (∀ (T T' T'' : LocLat S.G ℚ_[l] ↥S.LL.1 S.O) (U U' : ZMod S.n → Multiset ℤ) (e : T''.V ≃ₗ[↥S.LL.1] (T.V × T'.V)),
    (∀ σ x, e (T''.ρ σ x) = (T.ρ σ (e x).1, T'.ρ σ (e x).2)) → CrysWith (P.PD S.K) S.emb T.ρ U →
    CrysWith (P.PD S.K) S.emb T'.ρ U' → CrysWith (P.PD S.K) S.emb T''.ρ (fun i => U i + U' i)) ∧
  (∀ (T : LocLat S.G ℚ_[l] ↥S.LL.1 S.O) (U : ZMod S.n → Multiset ℤ) (θ : S.G →* S.Oˣ) (a : ZMod S.n → ℤ),
    CrysWith (P.PD S.K) S.emb T.ρ U → IsCrysChar (P.PD S.K) S.emb θ a →
    CrysWith (P.PD S.K) S.emb (twistRep T.ρ (chiLL ↥S.LL.1 θ)) (fun i => (U i).map (· + a i)) ∧
    IsCrysChar (P.PD S.K) S.emb θ⁻¹ (fun i => -a i)) ∧
  IsCrysChar (P.PD S.K) S.emb S.Γ.ε (fun _ => -1) ∧
  ∀ μ : S.G →* S.Oˣ, (Continuous fun σ => algebraMap S.O ↥S.LL.1 (μ σ)) → (∀ σ ∈ IK S.K, μ σ = 1) →
    IsCrysChar (P.PD S.K) S.emb μ (fun _ => 0)

end TopSit
end GlobalTheory.TopSteps
end
end

section

noncomputable section

namespace GlobalTheory.TypeLeaf

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.ArithmeticCylinders Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain

def SerLoc (D : D7) : Prop :=
  ∀ (i : D.nd.Loc) (σ' : D.ntypes.Par) (k : Fin 2) (v : D.nd.PlG k) (f : (ZMod (D.host.g k))[X]),
    ∀ F ∈ D.ntypes.MtPar (D.nd.mu i) (D.nd.j i) σ',
      D.ntypes.onMt (D.nd.mu i) (D.nd.j i) (atPlace D k v (D.ntypes.eSer k f)) F ≠ 0 → f = D.ntypes.labPar k σ' v

def TameOcc (D : D7) : Prop :=
  ∀ (σ : D.what₂.FT) (k : Fin 2) (v : D.nd.PlG k), D.ntypes.cuspidal σ →
    Formalism.MainNotions.N.TameGen D.nd (D.nd.plOm.1 (D.naut.plGw k v)) (D.ntypes.tg k v) →
    ∀ i : D.nd.Loc, D.nd.l i ≠ D.host.g k → D.what₂.isot (D.nd.j i) σ ≠ ⊥ → D.nd.goodRow σ →
      haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
      haveI : Fact (D.what₂.places.resChar (D.nd.w i)).Prime := ⟨D.what₂.places.resChar_prime (D.nd.w i)⟩
      Matrix.charpoly ((D.ntypes.rbar σ (D.nd.w i) (D.ntypes.tg k v) : GL (Fin D.R.r) _) :
          Matrix (Fin D.R.r) (Fin D.R.r) _) =
        ((Formalism.CyclotomicNorms.rootsBar (D.nd.lab k σ v)).map fun x =>
          X - C (D.ntypes.iota k v (D.nd.w i) (Formalism.CyclotomicNorms.primeToPart (D.what₂.places.resChar (D.nd.w i)) x))).prod ∧
      ∃ φ : G D.host.E D.nd.Om,
        D.ntypes.rbar σ (D.nd.w i) (φ * D.ntypes.tg k v * φ⁻¹) = D.ntypes.rbar σ (D.nd.w i) (D.ntypes.tg k v) ^ D.host.g k

abbrev redF (D : D7) (i : D.nd.Loc) (ρ : G D.host.E D.nd.Om →* GL (Fin D.R.r) (D.nd.O i)) :
    G D.host.E D.nd.Om →* GL (Fin D.R.r) (Formalism.CyclotomicNorms.Fbar (D.nd.l i)) :=
  mapRep ((D.naut.kFbar i).comp (IsLocalRing.residue (D.nd.O i))) ρ

def InjPrimeTo {A B : Type} [MonoidWithZero A] [Monoid B] (l : ℕ) (ι : A →* B) : Prop :=
  ∀ x y : A, x ≠ 0 → y ≠ 0 → (orderOf x).Coprime l → (orderOf y).Coprime l → ι x = ι y → x = y

abbrev labSig (D : D7) (Sig : List (Formalism.BasicNotions.Part D.naut.CG)) (k : Fin 2) (v : D.nd.PlG k) : (ZMod (D.host.g k))[X] :=
  D.naut.items₂ k (D.naut.plGw k v) (isoLoc D.nd D.naut Sig (D.naut.plGw k v))

def TameFixed (D : D7) (i : D.nd.Loc) (Sig : List (Formalism.BasicNotions.Part D.naut.CG))
    (ρ : G D.host.E D.nd.Om →* GL (Fin D.R.r) (D.nd.O i)) (k : Fin 2) : Prop :=
  haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  ∀ v : D.nd.PlG k, ∃ ι : Formalism.CyclotomicNorms.Fbar (D.host.g k) →* Formalism.CyclotomicNorms.Fbar (D.nd.l i), InjPrimeTo (D.nd.l i) ι ∧
    Matrix.charpoly ((redF D i ρ (D.ntypes.tg k v) : GL (Fin D.R.r) _) :
        Matrix (Fin D.R.r) (Fin D.R.r) (Formalism.CyclotomicNorms.Fbar (D.nd.l i))) =
      ((Formalism.CyclotomicNorms.rootsBar (labSig D Sig k v)).map fun x => X - C (ι (Formalism.CyclotomicNorms.primeToPart (D.nd.l i) x))).prod ∧
    ∃ φ : G D.host.E D.nd.Om,
      redF D i ρ (φ * D.ntypes.tg k v * φ⁻¹) = redF D i ρ (D.ntypes.tg k v) ^ D.host.g k

def TameAnyAt (D : D7) (i : D.nd.Loc) (Sig : List (Formalism.BasicNotions.Part D.naut.CG))
    (ρ : G D.host.E D.nd.Om →* GL (Fin D.R.r) (D.nd.O i)) (k : Fin 2) (w : PlE D.host) : Prop :=
  haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  ∃ (v : D.nd.PlG k) (j : Fin D.R.m) (ι : Formalism.CyclotomicNorms.Fbar (D.host.g k) →* Formalism.CyclotomicNorms.Fbar (D.nd.l i))
    (e₁ e₂ : ℤ), (e₁ = 1 ∨ e₁ = -1) ∧ (e₂ = 1 ∨ e₂ = -1) ∧ InjPrimeTo (D.nd.l i) ι ∧
    Matrix.charpoly ((redF D i ρ (D.nd.gam0 i w) : GL (Fin D.R.r) _) :
        Matrix (Fin D.R.r) (Fin D.R.r) (Formalism.CyclotomicNorms.Fbar (D.nd.l i))) =
      ((Formalism.CyclotomicNorms.rootsBar (labSig D Sig k v)).map
        fun x => X - C (ι (Formalism.CyclotomicNorms.primeToPart (D.nd.l i) x) ^ e₁)).prod ∧
    D.naut.kFbar i (IsLocalRing.residue (D.nd.O i) (chi1 D.nd i (D.nd.gam0 i w))) =
      ι (Formalism.CyclotomicNorms.primeToPart (D.nd.l i)
        (algebraMap (ZMod (D.host.g k)) (Formalism.CyclotomicNorms.Fbar (D.host.g k))
          ((D.nd.chiT k v j : (ZMod (D.host.g k))ˣ) : ZMod (D.host.g k)))) ^ e₂

def FullLab (D : D7) (Sig : List (Formalism.BasicNotions.Part D.naut.CG)) : Prop :=
  ∀ (k : Fin 2) (v : D.nd.PlG k), (labSig D Sig k v).natDegree =
    D.naut.lpDim (isoLoc D.nd D.naut Sig (D.naut.plGw k v))

def TameSum (D : D7) : Prop :=
  ∀ (i : D.nd.Loc) (Sig : List (Formalism.BasicNotions.Part D.naut.CG)), (∃ x, HasParamX D.nd D.naut i x Sig) → FullLab D Sig →
    IsCuspIso D.nd D.naut Sig →
    ∀ ρ : G D.host.E D.nd.Om →* GL (Fin D.R.r) (D.nd.O i), IsRepOfSig D.nd D.naut i Sig ρ →
    ∀ k : Fin 2, D.nd.l i ≠ D.host.g k → TameFixed D i Sig ρ k ∧
      ∀ w ∈ placesOver D.host.E (D.host.g k), TameGen D.nd (D.nd.plOm.1 w) (D.nd.gam0 i w) → TameAnyAt D i Sig ρ k w

def WildOne (D : D7) : Prop :=
  ∀ (k : Fin 2) (v : D.nd.PlG k) (L : D.naut.LP (D.naut.plGw k v)),
    (D.naut.items₂ k _ L).natDegree = D.naut.lpDim L →
      ∀ s ∈ Ine (F := D.host.E) (D.nd.plOm.1 (D.naut.plGw k v)),
        s ∈ wildSet D.nd (D.nd.plOm.1 (D.naut.plGw k v)) → D.naut.inePol L s = (X - 1) ^ D.naut.lpDim L

def FrobDense (D : D7) : Prop :=
  ∀ T : Set (PlE D.host), T.Finite → Dense {s : G D.host.E D.nd.Om | ∃ w : PlE D.host, w ∉ T ∧ IsSplitPl D.host w ∧
    ∃ B : ValuationSubring D.nd.Om, IsPlaceOver (F := D.host.E) B w ∧ IsFrob (F := D.host.E) B (normV w) s}

def PointPar (D : D7) : Prop :=
  ∀ (i : D.nd.Loc) (x : D.nd.X i) (π : D.naut.CG D.R.r), HasParamX D.nd D.naut i x [⟨D.R.r, π, 1⟩] →
    D.naut.csd π ∧ D.naut.ralg π

def RedVia (D : D7) (i : D.nd.Loc) (k : Fin 2)
    (ι : Fb (D.host.g k) (D.host.g_prime k) →* Formalism.CyclotomicNorms.Fbar (D.nd.l i)) : Prop :=
  ∀ (p : (D.nd.O i)[X]) (s : Multiset (Fb (D.host.g k) (D.host.g_prime k))),
    p.map (iotaO D.nd D.naut i) = (s.map fun x => X - C (D.ntypes.teichC k x)).prod →
    p.map ((D.naut.kFbar i).comp (IsLocalRing.residue (D.nd.O i))) = (s.map fun x => X - C (ι x)).prod

def TwistInv (D : D7) : Prop :=
  (∀ (a : ℕ) (π : D.naut.CG a), 1 ≤ a → D.naut.tw (D.naut.tw π D.naut.etaT) D.naut.etaTinv = π) ∧
  ∀ (a : ℕ) (π : D.naut.CG a), 1 ≤ a → D.naut.tw (D.naut.tw π D.naut.etaTinv) D.naut.etaT = π

def CharLaws (D : D7) : Prop :=
  ∀ (w : PlE D.host) (a χ χ' : D.naut.LP w), D.naut.lpDim χ = 1 → D.naut.lpDim χ' = 1 →
    D.naut.lpChar (D.naut.lpChar a χ) χ' = D.naut.lpChar a (D.naut.lpChar χ χ') ∧
    D.naut.lpChar a (D.naut.lpUnr w {1}) = a

def MultOne (D : D7) : Prop :=
  ∀ (a : ℕ) (π π' : D.naut.CG a), 1 ≤ a → (∀ w, D.naut.locG π w = D.naut.locG π' w) → π = π'

end GlobalTheory.TypeLeaf
end
end
