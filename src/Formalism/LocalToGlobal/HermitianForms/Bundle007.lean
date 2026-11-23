module

public import Formalism.LocalToGlobal.HermitianForms.Bundle005
public import Formalism.LocalToGlobal.HermitianColumns.TiedQC
public import Formalism.LocalToGlobal.HermitianForms.RankEqFirstLevel
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

open Formalism.BasicNotions NumberField IsDedekindDomain Matrix Formalism.UG
open scoped TensorProduct

namespace Formalism.L2.Forms

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {inQ : D.what₂.Tup → HeightOneSpectrum (𝓞 D.host.F) → Prop}

def redJ (F : ∀ u, FormsTied D u) (u : D.what₂.Word) (a : Fin 2) (v : HeightOneSpectrum (𝓞 D.host.F))
    (hv : (D.host.g a : 𝓞 D.host.F) ∈ v.asIdeal)
    (x : GL (Fin (D.sp.X (D.R.m - 1)).rank) (D.host.E ⊗[D.host.F] v.adicCompletion D.host.F)) :
    Matrix (Fin (D.R.N (D.R.m - 1))) (Fin (D.R.N (D.R.m - 1))) (kv D.host.F v) :=
  redM D.host.F v ((F u).gl.mat a v hv (((F u).glev (D.R.m - 1) (Nat.sub_le _ _)).fr a v hv)
    (reGL (rankN D (D.R.m - 1) (Nat.sub_le _ _)) _ x))



structure TwistedJointForms (T : Formalism.L2.Herm.TwChTied D inQ) (F : ∀ u, FormsTied D u) where

  J_g : ∀ u μ (h : 1 ≤ D.R.m - 1) (a : Fin 2) (v : HeightOneSpectrum (𝓞 D.host.F)) (hv : (D.host.g a : 𝓞 D.host.F) ∈ v.asIdeal),
    ∀ x ∈ levelVL D.sp.cm.sig (D.sp.X (D.R.m - 1)).gram v (T.levJ u μ h).Lb,
      x ∈ (T.levJ u μ h).Uloc v ↔ InJ (aOf D.R (D.R.m - 1)) D.R.t (D.R.N (D.R.m - 1)) false (redJ F u a v hv x)

  J_off : ∀ u μ (h : 1 ≤ D.R.m - 1) (v : HeightOneSpectrum (𝓞 D.host.F)), v ∉ T.Q μ → v ∉ badG D →
    ((T.levJ u μ h).Uloc v).map (reGL (rankN D (D.R.m - 1) (Nat.sub_le _ _)) _).toMonoidHom =
      ((F u).cls (D.R.m - 1) (Nat.sub_le _ _)).lev.Uloc v

  yG : ∀ u μ (h : 1 ≤ D.R.m - 1), T.Yb u μ h → ∀ (a : Fin 2) (v : HeightOneSpectrum (𝓞 D.host.F)),
    (D.host.g a : 𝓞 D.host.F) ∈ v.asIdeal → Fin (D.R.N (D.R.m - 1)) → kv D.host.F v
  yG_smul : ∀ u μ h (κ : (T.levJ u μ h).U) y a v hv,
    yG u μ h (κ • y) a v hv = redJ F u a v hv (bc (prV (E := D.host.E) v) κ.1) *ᵥ yG u μ h y a v hv

  yG_rep : ∀ u μ h β a v hv, yG u μ h (T.yb u μ h β) a v hv =
    fun b : Fin (D.R.N (D.R.m - 1)) => if (b : ℕ) = fcOf D.R (D.R.m - 1) then (1 : kv D.host.F v) else 0

  YQ : D.what₂.Word → D.what₂.Tup → 1 ≤ D.R.m - 1 → Type
  yQ : ∀ u μ h, T.Yb u μ h → YQ u μ h
  y_inj : ∀ u μ h y y', yG u μ h y = yG u μ h y' → yQ u μ h y = yQ u μ h y' → y = y'
  yQ_off : ∀ u μ h (κ : (T.levJ u μ h).U) y, (∀ v ∈ T.Q μ, bc (prV (E := D.host.E) v) κ.1 = 1) → yQ u μ h (κ • y) = yQ u μ h y

end Formalism.L2.Forms

end
end

section

noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain Matrix Formalism.UG
open scoped TensorProduct

namespace Formalism.L2.Forms

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

structure TwAtT (Tw : TwForms D) (u : D.what₂.Word) (μ : D.what₂.Tup) where

  eVT : (Tw.A u μ).vT ≃ (D.mem u).A.vT

  eFv : ∀ v, (Tw.A u μ).Fv v ≃+* (D.mem u).A.Fv (eVT v)
  psiT : ∀ v x, (Tw.A u μ).psiT v x = (D.mem u).A.psiT (eVT v) (eFv v x)
  rhoT : ∀ v a φ, (Tw.A u μ).rhoT v a (D.e0Tw u μ φ) =
    D.e0Tw u μ ((D.mem u).A.rhoT (eVT v) (Units.map ((eFv v : (Tw.A u μ).Fv v ≃+* (D.mem u).A.Fv (eVT v)) : (Tw.A u μ).Fv v →* (D.mem u).A.Fv (eVT v)) a) φ)
  Mu0 : (Tw.A u μ).Mu0 = (D.mem u).A.Mu0.map (D.e0Tw u μ : _ →ₗ[ℂ] _)
  duStar : (Tw.A u μ).duStar = (D.mem u).A.duStar
  Dstar : (Tw.A u μ).Dstar = (D.mem u).A.Dstar
  GamP : (Tw.A u μ).GamP = (D.mem u).A.GamP

  tauOf : ∀ w, D.what₂.places.resChar w = (D.mem u).A.T → ∀ v, (Tw.fm u μ).tauOf w v = (D.fm u).tauOf w (eVT v)
  seenP : ∀ w, D.what₂.places.resChar w = (D.mem u).A.T → (Tw.fm u μ).seenP w = (D.fm u).seenP w

def TwAtT.eV {Tw : TwForms D} {u : D.what₂.Word} {μ : D.what₂.Tup} (a : TwAtT Tw u μ) (At : AtTTied u) :
    (Tw.A u μ).vT ≃ PlT D u := a.eVT.trans At.eV

def TwAtT.res {Tw : TwForms D} {u : D.what₂.Word} {μ : D.what₂.Tup} (a : TwAtT Tw u μ) (At : AtTTied u) (v : (Tw.A u μ).vT) :
    𝓞 D.host.E →+* (Tw.A u μ).Fv v := ((a.eFv v).symm : _ →+* _).comp (At.res (a.eVT v))

variable {inQ : D.what₂.Tup → HeightOneSpectrum (𝓞 D.host.F) → Prop}

def okQ (D : D7) (Q : Finset (HeightOneSpectrum (𝓞 D.host.F))) (w : D.what₂.places.Pl) : Prop :=
  ∀ v ∈ Q, ((D.what₂.places.resChar w : ℕ) : 𝓞 D.host.F) ∉ v.asIdeal

def twY (T : Formalism.L2.Herm.TwChTied D inQ) (F : ∀ u, FormsTied D u) (u : D.what₂.Word) (μ : D.what₂.Tup) (i : ℕ) (hi : i ≤ D.R.m) :
    (D.chTw u μ).Y i ≃ Fr D i hi :=
  (T.eY u μ i hi).symm.trans ((F u).val i hi).eY



structure TwFormsTied (D : D7) (Tw : TwForms D) {inQ : D.what₂.Tup → HeightOneSpectrum (𝓞 D.host.F) → Prop}
    (T : Formalism.L2.Herm.TwChTied D inQ) (F : ∀ u, FormsTied D u) where

  atT : ∀ u μ, TwAtT Tw u μ

  ch : ∀ (u : D.what₂.Word) (μ : D.what₂.Tup), μ ≠ D.what₂.mu0 → ∀ (i : ℕ), 1 ≤ i → ∀ (hm : i ≤ D.R.m) (β : T.Ch u μ i),
    LevelChart D (D.mem u).A.T (badQ D (T.Q μ)) i hm
      (fun c : {c // T.chOf u μ i c = β} => (D.chTw u μ).stab i c.1) (fun c => latCrd D i hm (T.lat u μ i c.1))

  car : ∀ u μ (hμ : μ ≠ D.what₂.mu0) i (h1 : 1 ≤ i) (hm : i ≤ D.R.m) (β : T.Ch u μ i),
    SameCar (rankN D i hm) (T.lev u μ i h1 hm β).Lb (ch u μ hμ i h1 hm β).lev.Lb
      (T.lev u μ i h1 hm β).Uloc (ch u μ hμ i h1 hm β).lev.Uloc (T.lev u μ i h1 hm β).U (ch u μ hμ i h1 hm β).lev.U
      (fun c => ((T.cls u μ hμ i h1 hm β).y c).1) (fun c => ((ch u μ hμ i h1 hm β).y c).1)
      (fun c s => ((T.cls u μ hμ i h1 hm β).stabI c s).1) (fun c s => ((ch u μ hμ i h1 hm β).stabI c s).1)

  chi_fin : ∀ u μ hμ i h1 hm β, ∃ n : ℕ, 0 < n ∧ ∀ κ, (ch u μ hμ i h1 hm β).lev.chi κ ^ n = 1

  chi_off : ∀ u μ hμ i h1 hm β (κ : (ch u μ hμ i h1 hm β).lev.U) (κ' : ((F u).cls i hm).lev.U), κ.1 = κ'.1 →
    (∀ v ∈ T.Q μ, bc (prV (E := D.host.E) v) κ.1 = 1) → (ch u μ hμ i h1 hm β).lev.chi κ = ((F u).cls i hm).lev.chi κ'

  chiJ : ∀ u μ (h : 1 ≤ D.R.m - 1), (T.levJ u μ h).U →* ℂˣ
  chiJ_eq : ∀ u μ hμ (h : 1 ≤ D.R.m - 1) β (κ : (T.levJ u μ h).U)
    (κ' : (ch u μ hμ (D.R.m - 1) h (Nat.sub_le _ _) β).lev.U), κ'.1 = reGL (rankN D (D.R.m - 1) (Nat.sub_le _ _)) _ κ.1 →
    (ch u μ hμ (D.R.m - 1) h (Nat.sub_le _ _) β).lev.chi κ' = chiJ u μ h κ

  val : ∀ u μ hμ i h1 hm, ValuationCompatibleChart (Tw.fm u μ) (twY T F u μ i hm) (okQ D (T.Q μ)) (T.chOf u μ i)
    (lat := fun c => latCrd D i hm (T.lat u μ i c)) (ch u μ hμ i h1 hm)

  dil : ∀ u μ hμ i h1 hm, DilationCompatibleChart (Tw.fm u μ) (twY T F u μ i hm) ((atT u μ).eV (F u).atT) (T.chOf u μ i)
    (lat := fun c => latCrd D i hm (T.lat u μ i c)) (ch u μ hμ i h1 hm)

  ipV : ∀ u μ i hi, IpVTieG (Tw.fm u μ) (twY T F u μ i hi)

  norm : ∀ u μ i hi, NormTieG (Tw.fm u μ) (twY T F u μ i hi)

  twisted_e0_at_mu0_eq_eMu0 : ∀ u x, Tw.e0 u D.what₂.mu0 x = Tw.eMu0 u 0 (Nat.zero_le _) x

end Formalism.L2.Forms

end
end

section

open Formalism.BasicNotions NumberField IsDedekindDomain Matrix Formalism.UG

namespace Formalism.L2.Forms

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem reGL_rfl {a : ℕ} (R : Type) [CommRing R] (x : GL (Fin a) R) : reGL rfl R x = x := by
  apply Units.ext
  ext i j
  simp [reGL]

theorem reV_rfl {a : ℕ} (E : Type) [Field E] (x : Fin a → E) : reV rfl E x = x := by
  ext i
  simp [reV]

theorem reL_rfl {a : ℕ} {E : Type} [Field E] [NumberField E] (L : Submodule (𝓞 E) (Fin a → E)) : reL rfl L = L := by
  ext z
  simp [reL, reV_rfl]

theorem Joint.Pv {D : D7} {X : Formalism.L2.Herm.ColsHerm D} {u : D.what₂.Word} {T : FormsTied D u} (J : Joint X u T)
    (v : (D.mem u).A.vT) : T.atT.Pv v = (X.atT u).Pv v := by
  unfold AtTTied.Pv
  rw [J.res]
  exact (X.atT u).res_ker v

end Formalism.L2.Forms
end
