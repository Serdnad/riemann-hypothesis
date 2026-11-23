module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle011
public import Formalism.SharpRestriction.LevelLetterCocycles.PairedCharacterCondition
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle015
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.HCFFromRecipA

@[expose] public section

section

noncomputable section

namespace GlobalTheory.PendOf

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open Polynomial Module TensorProduct Formalism.MainNotions.PairedCharacterCondition

structure TameOm (D : D7) where
  om : ∀ k : Fin 2, PlE D.host → Fb (D.host.g k) (D.host.g_prime k) → GE D.nd → ℂ
  om_one : ∀ k w x, x ≠ 0 → om k w x 1 = 1
  om_mul : ∀ k w x, x ≠ 0 → ∀ σ ∈ Ine (F := D.host.E) (D.nd.plOm.1 w),
    ∀ σ' ∈ Ine (F := D.host.E) (D.nd.plOm.1 w), om k w x (σ * σ') = om k w x σ * om k w x σ'
  tameInertiaChar_mul_root : ∀ k w x y, x ≠ 0 → y ≠ 0 → ∀ σ ∈ Ine (F := D.host.E) (D.nd.plOm.1 w),
    om k w (x * y) σ = om k w x σ * om k w y σ
  om_wild : ∀ k, ∀ w ∈ placesOver D.host.E (D.host.g k), ∀ x, x ≠ 0 →
    ∀ σ ∈ wildSet D.nd (D.nd.plOm.1 w), om k w x σ = 1
  om_open : ∀ k w x, x ≠ 0 → ∃ U : Subgroup (GE D.nd), IsOpen (U : Set (GE D.nd)) ∧
    ∀ σ ∈ U, σ ∈ Ine (F := D.host.E) (D.nd.plOm.1 w) → om k w x σ = 1
  om_inj : ∀ k, ∀ w ∈ placesOver D.host.E (D.host.g k), ∀ x y, x ≠ 0 → y ≠ 0 → x ≠ y →
    ∃ σ ∈ Ine (F := D.host.E) (D.nd.plOm.1 w), om k w x σ ≠ om k w y σ
  om_tg : ∀ k (v : D.nd.PlG k) x, x ≠ 0 →
    om k (D.naut.plGw k v) x (D.ntypes.tg k v) = D.ntypes.teichC k x

def LabIne {D : D7} (Ω : TameOm D) : Prop :=
  ∀ k, ∀ w ∈ placesOver D.host.E (D.host.g k), ∀ L : D.naut.LP w,
    (D.naut.items₂ k w L).natDegree = D.naut.lpDim L →
    haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
    ∀ σ ∈ Ine (F := D.host.E) (D.nd.plOm.1 w), D.naut.inePol L σ =
      ((Formalism.CyclotomicNorms.rootsBar (D.naut.items₂ k w L)).map fun x => X - C (Ω.om k w x σ)).prod

def LabChar (D : D7) : Prop :=
  ∀ k, ∀ w ∈ placesOver D.host.E (D.host.g k), ∀ (L χ : D.naut.LP w)
    (u : (ZMod (D.host.g k))ˣ), (D.naut.items₂ k w L).natDegree = D.naut.lpDim L →
    D.naut.lpDim χ = 1 → D.naut.items₂ k w χ = X - C (u : ZMod (D.host.g k)) →
    haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
    (D.naut.items₂ k w (D.naut.lpChar L χ)).natDegree = D.naut.lpDim L ∧
    Formalism.CyclotomicNorms.rootsBar (D.naut.items₂ k w (D.naut.lpChar L χ)) =
      (Formalism.CyclotomicNorms.rootsBar (D.naut.items₂ k w L)).map
        (· * algebraMap (ZMod (D.host.g k)) (Formalism.CyclotomicNorms.Fbar (D.host.g k)) (u : ZMod (D.host.g k)))

def IneRep (D : D7) : Prop :=
  ∀ k : Fin 2, ∀ w ∈ placesOver D.host.E (D.host.g k), ∀ L : D.naut.LP w,
    ∃ ρ : ↥(Ine (F := D.host.E) (D.nd.plOm.1 w)) →* GL (Fin (D.naut.lpDim L)) ℂ,
      (∃ U : Subgroup (GE D.nd), IsOpen (U : Set (GE D.nd)) ∧
        ∀ σ : ↥(Ine (F := D.host.E) (D.nd.plOm.1 w)), (σ : GE D.nd) ∈ U → ρ σ = 1) ∧
      ∀ σ : ↥(Ine (F := D.host.E) (D.nd.plOm.1 w)), D.naut.inePol L (σ : GE D.nd) =
        ((ρ σ : GL (Fin (D.naut.lpDim L)) ℂ) : Matrix (Fin (D.naut.lpDim L)) (Fin (D.naut.lpDim L)) ℂ).charpoly

def TameLP (D : D7) {w : PlE D.host} (L : D.naut.LP w) : Prop :=
  ∀ σ ∈ Ine (F := D.host.E) (D.nd.plOm.1 w), σ ∈ wildSet D.nd (D.nd.plOm.1 w) →
    D.naut.inePol L σ = (X - 1) ^ D.naut.lpDim L

def LabDepth (D : D7) : Prop :=
  ∀ k : Fin 2, ∀ w ∈ placesOver D.host.E (D.host.g k), ∀ L : D.naut.LP w,
    (D.naut.items₂ k w L).Monic ∧ ((D.naut.items₂ k w L).natDegree = D.naut.lpDim L ↔ TameLP D L)

def GenFam (D : D7) (γ : Fin 2 → PlE D.host → GE D.nd) : Prop :=
  (∀ k v, γ k (D.naut.plGw k v) = D.ntypes.tg k v) ∧
    ∀ k : Fin 2, ∀ w ∈ placesOver D.host.E (D.host.g k), TameGenAt (D.nd.plOm.1 w) (γ k w)

def LabGen (D : D7) : Prop :=
  ∃ γ : Fin 2 → PlE D.host → GE D.nd, GenFam D γ ∧
    ∀ k : Fin 2, ∀ w ∈ placesOver D.host.E (D.host.g k), ∀ L : D.naut.LP w,
      (D.naut.items₂ k w L).natDegree = D.naut.lpDim L →
      haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
      D.naut.inePol L (γ k w) =
        ((Formalism.CyclotomicNorms.rootsBar (D.naut.items₂ k w L)).map fun x => X - C (D.ntypes.teichC k x)).prod

def DepthZ (D : D7) : Prop :=
  ∀ (i : D.nd.Loc) (PI : D.naut.AV i) (k : Fin 2), ∀ w ∈ placesOver D.host.E (D.host.g k),
    TameLP D (D.naut.locV i PI w)

structure CenO (D : D7) where
  zO : ∀ i : D.nd.Loc,
    ↥(Subalgebra.center (D.nd.O i) (MonoidAlgebra (D.nd.O i) (G0g D.nd))) →ₐ[D.nd.O i]
      Module.End (D.nd.O i) (D.nd.Mt i)
  zO_comm : ∀ i z (f : D.nd.T i), zO i z * D.nd.act i f = D.nd.act i f * zO i z
  zO_act : ∀ i (z : ↥(Subalgebra.center (D.nd.O i) (MonoidAlgebra (D.nd.O i) (G0g D.nd))))
    (x y : D.what₂.MtL (D.nd.mu i) (D.nd.j i)),
    D.what₂.jMt _ _ y = D.ntypes.onMt (D.nd.mu i) (D.nd.j i)
      (mapCoef (iotaO D.nd D.naut i) (z : MonoidAlgebra (D.nd.O i) (G0g D.nd))) (D.what₂.jMt _ _ x) →
    D.nd.prMt i y = (zO i z).baseChange (KK D.nd i) (D.nd.prMt i x)

def ZLStable (D : D7) : Prop :=
  ∀ (i : D.nd.Loc) (z : MonoidAlgebra D.what₂.LL (G0g D.nd)), (∀ a, z * a = a * z) →
    ∀ x : D.what₂.MtL (D.nd.mu i) (D.nd.j i), ∃ y : D.what₂.MtL (D.nd.mu i) (D.nd.j i),
      D.what₂.jMt _ _ y =
        D.ntypes.onMt (D.nd.mu i) (D.nd.j i) (mapCoef D.what₂.embLL z) (D.what₂.jMt _ _ x)

def CenInt (D : D7) : Prop :=
  ∀ (i : D.nd.Loc) (z : MonoidAlgebra ℤ (G0g D.nd)), (∀ a, z * a = a * z) →
    ∀ x ∈ GlobalTheory.EtaJoin.genSet D (D.nd.mu i) (D.nd.j i), ∃ y ∈ GlobalTheory.EtaJoin.lat D (D.nd.mu i) (D.nd.j i),
      D.what₂.jMt _ _ y =
        D.ntypes.onMt (D.nd.mu i) (D.nd.j i) (mapCoef (Int.castRingHom ℂ) z) (D.what₂.jMt _ _ x)

def OnMtPreservesTypeV (D : D7) : Prop :=
  ∀ (i : D.nd.Loc) (PI : D.naut.AV i) (z : MonoidAlgebra ℂ (G0g D.nd)), ∀ F ∈ D.naut.typeV i PI,
    D.ntypes.onMt (D.nd.mu i) (D.nd.j i) z F ∈ D.naut.typeV i PI

def typeSum (D : D7) (i : D.nd.Loc) (o : Option (D.nd.X i)) : Submodule ℂ (D.what₂.Mt (D.nd.mu i) (D.nd.j i)) :=
  ⨆ P ∈ {P | D.naut.ptV i P = o}, D.naut.typeV i P

structure Sec (D : D7) (i : D.nd.Loc) where

  Φ : TensorProduct (D.nd.O i) (KK D.nd i) (D.nd.Mt i) →+ D.what₂.Mt (D.nd.mu i) (D.nd.j i)
  inj : Function.Injective Φ
  semi : ∀ (k : KK D.nd i) v, Φ (k • v) = (D.naut.iotaQC i (D.naut.iotaQ i k)) • Φ v
  eig : ∀ x, ∀ u ∈ heckeEig (D.nd.T i) (D.nd.act i) x, Φ u ∈ typeSum D i (some x)
  split : ∀ y : D.what₂.MtL (D.nd.mu i) (D.nd.j i), D.what₂.jMt _ _ y - Φ (D.nd.prMt i y) ∈ typeSum D i none

def PrType (D : D7) : Prop :=
  ∀ i (PI : D.naut.AV i) (x : D.what₂.MtL (D.nd.mu i) (D.nd.j i)),
    D.what₂.jMt _ _ x ∈ D.naut.typeV i PI →
    (∀ p, D.naut.ptV i PI = some p → D.nd.prMt i x ∈ heckeEig (D.nd.T i) (D.nd.act i) p) ∧
    (D.naut.ptV i PI = none → D.nd.prMt i x = 0)

def ParSurj (D : D7) : Prop :=
  ∀ i x Sig, HasParamX D.nd D.naut i x Sig →
    ∃ σ' : D.ntypes.Par, ∀ w, D.ntypes.locPar σ' w = isoLoc D.nd D.naut Sig w

def SerLL (D : D7) : Prop :=
  ∀ (k : Fin 2) (f : (ZMod (D.host.g k))[X]) (h : GL (Fin D.R.r) (ZMod (D.host.g k))),
    ∃ y : D.what₂.LL, D.what₂.embLL y = (D.ntypes.eSer k f).coeff h

def CoeffRingsHaveRootsOfUnity (D : D7) : Prop := ∀ i : D.nd.Loc, ∃ ζ : D.nd.O i, IsPrimitiveRoot ζ D.what₂.restRowsFiniteGroupCard


open Classical in
def SerEq (D : D7) (lz : ∀ k : Fin 2, LzData (D.host.g k)) : Prop :=
  ∀ (k : Fin 2) (f : (ZMod (D.host.g k))[X]),
    D.ntypes.eSer k f = ∑ τ : (lz k).Irr D.R.r, if (lz k).lab τ = f then (lz k).idem τ else 0

def mk {D : D7} (lz : ∀ k : Fin 2, LzData (D.host.g k)) (h1 : SerEq D lz) (h2 : SerLL D) (h3 : CoeffRingsHaveRootsOfUnity D)
    (Ω : TameOm D) (h4 : LabIne Ω) (h5 : LabChar D) (Z : CenO D) (h6 : ZLStable D) (h7 : PrType D)
    (h8 : ParSurj D) : Pend D where
  lz := lz
  eSer_eq := h1
  eSer_LL := h2
  zetaPrimitiveRoot := h3
  om := Ω.om
  om_one := Ω.om_one
  om_mul := Ω.om_mul
  tameInertiaChar_mul_root := Ω.tameInertiaChar_mul_root
  om_wild := Ω.om_wild
  om_open := Ω.om_open
  om_inj := Ω.om_inj
  om_tg := Ω.om_tg
  inertiaCharpoly_eigenvalues := h4
  inertiaCharpoly_character := h5
  zO := Z.zO
  zO_comm := Z.zO_comm
  zL_stable := h6
  zO_act := Z.zO_act
  prMt_type := h7
  Par_surj := h8
  kty i PI k v := {τ | ∃ F ∈ D.naut.typeV i PI, D.ntypes.onMt (D.nd.mu i) (D.nd.j i)
      (Formalism.MainNotions.ArithmeticCylinders.atPlace D k v ((lz k).idem τ)) F ≠ 0}
  kty_spec _ _ _ _ _ := Iff.rfl

end GlobalTheory.PendOf

end
end

section

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.CuspRep

namespace GlobalTheory.RSJ.Model

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

def eLast (R : Type*) [CommRing R] (a : ℕ) : Fin a → R := fun i => if (i : ℕ) + 1 = a then 1 else 0

theorem secRow_eLast {R : Type*} [CommRing R] : secRow (eLast R a) = 1 := by
  ext i j
  simp only [secRow, eLast, Matrix.of_apply, Matrix.one_apply]
  by_cases h : (i : ℕ) + 1 = a
  · rw [if_pos h]
    by_cases h2 : (j : ℕ) + 1 = a
    · rw [if_pos h2, if_pos (Fin.ext (by omega))]
    · rw [if_neg h2, if_neg (fun e : i = j => h2 (e ▸ h))]
  · rw [if_neg h]



omit [NumberField E] [_root_.NumberField.IsTotallyComplex E] in
theorem secInv_eLast : secInv (eLast (Cinf E) a) = 1 := by
  unfold secInv
  split_ifs with h
  · rw [inv_eq_one]; exact Units.ext secRow_eLast
  · rfl


omit [_root_.NumberField.IsTotallyComplex E] in
theorem detPow_mul (x : ℝ) (g h : GA E a) : detPow E a x (g * h) = detPow E a x g * detPow E a x h := by
  simp [detPow]



omit [_root_.NumberField.IsTotallyComplex E] in
theorem detPow_ratGL (x : ℝ) (γ : GL (Fin a) E) : detPow E a x (ratGL E a γ) = 1 := by
  have h : Matrix.GeneralLinearGroup.det (ratGL E a γ) = diagUnits E (Matrix.GeneralLinearGroup.det γ) :=
    Units.ext (det_map (algebraMap E (Ad E)) γ)
  have h2 := (GlobalTheory.HeckeGal.Model.absPow E x).2.2 (Matrix.GeneralLinearGroup.det γ)
  unfold detPow chiDet
  rw [MonoidHom.comp_apply, h, h2]; simp








end GlobalTheory.RSJ.Model
end
end

section

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.ResSel

namespace GlobalTheory.StepTwo

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N} (bkP : BKPh X)
  (i : X.Tw) (s : X.Sig i)

def idl : Ideal (X.O0 i) := Ideal.span {(X.l i : X.O0 i) ^ nu X i} * IsLocalRing.maximalIdeal (X.O0 i)

def Small2 (M : ℕ) (L : Subgroup (GE N)) (z : GE N) : Prop :=
  Small i s L z ∧ (∀ g ∈ L, ∀ ζ : N.Om, ζ ^ (2 * X.l i ^ M) = 1 → g ζ = ζ) ∧ ∀ g ∈ L, ∀ a b, (Tmat i s g - 1) a b ∈ idl i

variable (M : ℕ) {R n : ℕ} (d : PlE D.host → (GE N →* Multiplicative (ZMod (X.l i ^ M))))

def PiLocalization₂ (A : Finset (PlE D.host)) (L : Subgroup (GE N)) (z : GE N) (P : Fin R ⊕ Fin n → PlE D.host) : Prop :=
  SlopeTestRemainingChoices X i M A P (fun q => d (P q)) ∧
    (∀ a, (∀ v, Over (P (.inl a)) v → ∀ B : ValuationSubring N.Om, IsPlaceOver B v → Ine (F := D.host.E) B ≤ L) ∧
      ∀ σ : GE N, IsFrob (N.plOm.1 (P (.inl a))) (normV (P (.inl a))) σ → ∃ g : GE N, g * σ * g⁻¹ * z⁻¹ ∈ L) ∧
    ∀ a, DecV N (P (.inr a)) ≤ L ∧ ∀ (b : Fin R) (σ : GE N), IsFrob (N.plOm.1 (P (.inr a))) (normV (P (.inr a))) σ →
      d (P (.inl b)) σ = Multiplicative.ofAdd (if a.val = b.val then 1 else 0)

def NF (P : Fin R ⊕ Fin n → PlE D.host) (c : ℕ) : Prop :=
  ∀ Q, IsQ P Q → ∀ (a : ℕ) (Φ : Matrix (Fin a) (Fin a) (abelian₂ X i M (Fin R ⊕ Fin n))),
    Computes bkP i s M (fun q => d (P q)) Q Φ → ∀ F, toLam X i M (Fin R ⊕ Fin n) F = Φ.det →
      ∃ m : Fin R ⊕ Fin n →₀ ℕ, m.degree < c ∧ F.coeff m ∉ idl i

def NFit (P : Fin R ⊕ Fin n → PlE D.host) (c : ℕ) : Prop :=
  ∀ Q, IsQ P Q → ∀ (a : ℕ) (Φ : Matrix (Fin a) (Fin a) (abelian₂ X i M (Fin R ⊕ Fin n))),
    Computes bkP i s M (fun q => d (P q)) Q Φ → a = 0 ∨ ∃ b b', ∀ F, toLam X i M (Fin R ⊕ Fin n) F = Φ.adjugate b b' →
      ∃ m : Fin R ⊕ Fin n →₀ ℕ, m.degree < c ∧ (∀ j : Fin R, n ≤ j.val → m (.inl j) = 0) ∧ IsUnit (F.coeff m)

def Ext (P : Fin R ⊕ Fin n → PlE D.host) (P' : Fin R ⊕ Fin (n + 1) → PlE D.host) : Prop :=
  ∀ q, P' (Sum.map id Fin.castSucc q) = P q

def Start : Prop :=
  ∀ (M R n : ℕ) d A L z (P : Fin R ⊕ Fin n → PlE D.host) (φ φ' : Fin n → GE N), n ≤ R → 4 * D.R.r * n + 2 < X.l i ^ M →
    IsTameInertiaElementAtTwistPrime X i z → Small i s L z → PiLocalization₂ i M d A L z P →
    (∀ a, IsFrob (N.plOm.1 (P (.inr a))) (normV (P (.inr a))) (φ a) ∧ IsCj X (φ a) (φ' a)) → Corank bkP i s φ φ' 1 →
    NFit bkP i s M d P (4 * D.R.r * n + 1)

def Grow : Prop :=
  0 < nu X i → ∀ (M R n : ℕ) d A L z (P : Fin R ⊕ Fin n → PlE D.host) (P' : Fin R ⊕ Fin (n + 1) → PlE D.host) (c : ℕ), n < R →
    c + 2 * D.R.r ≤ X.l i ^ (M - nu X i - 1) → nu X i + 2 ≤ M → IsTameInertiaElementAtTwistPrime X i z → Small2 i s M L z → PiLocalization₂ i M d A L z P' → Ext P P' →
    (NF bkP i s M d P c → NF bkP i s M d P' (c + 2 * D.R.r)) ∧ (NFit bkP i s M d P c → NFit bkP i s M d P' (c + 2 * D.R.r))

def Step : Prop :=
  0 < nu X i → ∀ (M R n : ℕ) H S d A L z (P : Fin R ⊕ Fin n → PlE D.host) (w e : ℕ), n < R →
    IsDiscreteValuationRing.addVal (X.O0 i) ((X.l i : X.O0 i) ^ nu X i) = e →
    2 * (e + 1) * w + 2 + 2 * D.R.r ≤ X.l i ^ (M - nu X i - 1) → nu X i + 2 ≤ M →
    AdmFam X i M H S d → L ≤ H → IsTameInertiaElementAtTwistPrime X i z → Small2 i s M L z → PiLocalization₂ i M d A L z P → NFit bkP i s M d P (w + 1) →
    ∃ P' : Fin R ⊕ Fin (n + 1) → PlE D.host, Ext P P' ∧ PiLocalization₂ i M d A L z P' ∧
      NF bkP i s M d P' (2 * (e + 1) * w + 2 + 2 * D.R.r)

end GlobalTheory.StepTwo
end
end
