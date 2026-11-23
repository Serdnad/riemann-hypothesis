module

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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open scoped TensorProduct InnerProductSpace

namespace Formalism.IndefR.Links
attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

section Links

open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

namespace RealDat

variable (R : RealDat D A Ks) (F : Face D A)

abbrev num (C CH : ℝ) : IndefNum A.fam.base := (F.fc (R.toCx F).zs).Z.num C CH

def LPos : Prop := ∀ b, (lv (F.fc (R.toCx F).zs) b).Pos

def LUnif : Prop :=
  ∀ i σ, (∀ (n : ℕ) (b : Fin n → (Fin (R.nW i) → D.what₂.LL)), LinearIndependent D.what₂.LL b →
      LinearIndependent ℂ fun k => (R.FW i).j σ (b k)) ∧
    Submodule.span ℂ (Set.range ((R.FW i).j σ)) = ⊤ ∧
    ∀ g x, (R.HW i σ).e ((R.FW i).j σ ((R.FW i).ρ g x)) = σ (((R.FW i).chi g : D.what₂.LLˣ) : D.what₂.LL) •
      postOn _ (actL (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g)) ((R.HW i σ).e ((R.FW i).j σ x))

def LLevelW : Prop := ∀ b i σ, R.WS F b i σ = (R.Wat i σ (R.levL F b σ)).comap (R.HW i σ).e

def LIntegral : Prop := ∀ i, (R.FW i).IsKsForm ∧ (R.FW i).MKFull ∧ (R.FW i).MKStable

variable {R F}

end RealDat


namespace RealDat

variable {R : RealDat D A Ks} {F : Face D A}

theorem nP_pos (b : Bool) : 0 < nP F b := by
  unfold nP
  exact_mod_cast Nat.card_pos

theorem h0 (h : R.IsTup F) : (R.toCx F).H0 := by
  refine ⟨h.mu_conj, fun w => ⟨fun hw => h.mu_ne w hw, fun hne => ?_⟩⟩
  by_contra hw
  exact hne (h.mu_off w hw)

theorem ewNorm (b : Bool) : (R.toCx F).EWnorm b := by
  intro j x y
  show cj _ (inner ℂ ((((Real.sqrt (nP F b) : ℝ) : ℂ)) • ((Tw.out x : R.WS F b j (sg0 D A)) : (R.HW j (sg0 D A)).H))
      ((((Real.sqrt (nP F b) : ℝ) : ℂ)) • ((Tw.out y : R.WS F b j (sg0 D A)) : (R.HW j (sg0 D A)).H))) =
    ((nP F b : ℝ) : ℂ) * cj _ (inner ℂ ((Tw.out x : R.WS F b j (sg0 D A)) : (R.HW j (sg0 D A)).H)
      ((Tw.out y : R.WS F b j (sg0 D A)) : (R.HW j (sg0 D A)).H))
  rw [inner_smul_left, inner_smul_right, Complex.conj_ofReal, ← mul_assoc, ← Complex.ofReal_mul,
    Real.mul_self_sqrt (nP_pos b).le, map_mul, cj_ofReal]
  rfl

theorem kForm (hU : R.LUnif) (b : Bool) : (R.toCx F).KForm b := by
  intro j v
  have hc : (((Real.sqrt (nP F b))⁻¹ : ℝ) : ℂ) ≠ 0 := by
    have := Real.sqrt_pos.2 (nP_pos (F := F) b)
    exact_mod_cast (inv_pos.2 this).ne'
  have hL : LinearIndependent D.what₂.LL (R.bL F b j) :=
    (Module.finBasis D.what₂.LL (R.WL F b j)).linearIndependent.map' (R.WL F b j).subtype (Submodule.ker_subtype _)
  have h1 : LinearIndependent ℂ (R.bC F b j (sgAt D.what₂.embLL v)) :=
    ((hU j _).1 _ _ hL).units_smul fun _ => Units.mk0 _ hc
  have h2 := linearIndependent_span h1
  have h3 : Submodule.span ℂ (Set.range fun k => (⟨R.bC F b j (sgAt D.what₂.embLL v) k, Submodule.subset_span ⟨k, rfl⟩⟩ :
      R.WS F b j (sgAt D.what₂.embLL v))) = ⊤ := Submodule.span_range_subtype_eq_top_iff _ _ |>.2 rfl
  exact ⟨Tw.linInd (E := R.WS F b j (sgAt D.what₂.embLL v)) _ h2, Tw.span_top (E := R.WS F b j (sgAt D.what₂.embLL v)) _ h3⟩

end RealDat

end Links

end Formalism.IndefR.Links

end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open scoped TensorProduct InnerProductSpace

namespace Formalism.IndefR.Links

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def OrZero {X : Type} [Zero X] (p : X → Prop) (x : X) : Prop := ((∃ y, p y) → p x) ∧ ((¬ ∃ y, p y) → x = 0)

theorem orZero_exists {X : Type} [Zero X] (p : X → Prop) : ∃ x, OrZero p x := by
  by_cases h : ∃ y, p y
  · obtain ⟨y, hy⟩ := h
    exact ⟨y, fun _ => hy, fun hn => absurd ⟨y, hy⟩ hn⟩
  · exact ⟨0, fun h' => absurd h' h, fun _ => rfl⟩

section Weak

open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

namespace RealDat

variable (R : RealDat D A Ks)

def PItY (k : ℕ) (It : type_of% (R.ItY k)) : Prop := ∀ t, IsItW R.θ (R.MY k) (R.MY (k + 1)) (R.ωY t k) (R.ptY t k) It

def PItX (It : type_of% R.ItX) : Prop := ∀ t, IsItW R.θ (R.MY (D.R.m - 1)) R.MX (R.ωX t) (R.ptX t) It

def PIoY (t : T) (k : ℕ) (io : R.CC t (k + 1) →ₗ[ℂ] R.CC t k) : Prop :=
  Lift.IsIo (R.νY t (k + 1)) (R.fdY t (k + 1)) (thetaKO (R.ωY t k)) (R.ptY t k) (R.ItY k) (R.CC t (k + 1)) (R.CC t k) io

def PIoX (t : T) (io : LinearMap.range (R.cX.toMap R.prX ∘ₗ (R.HX t).e) →ₗ[ℂ] R.CC t (D.R.m - 1)) : Prop :=
  Lift.IsIo (R.νX t) (R.fdX t) (thetaKO (R.ωX t)) (R.ptX t) R.ItX (LinearMap.range (R.cX.toMap R.prX ∘ₗ (R.HX t).e))
    (R.CC t (D.R.m - 1)) io

def PTh (t : T) (g : (R.HX t).H →ₗ[ℂ] R.HE.H) : Prop :=
  ∀ x, R.HE.e (g x) = postOn (R.MY 0) R.e0 (PiTensorProduct.lift.symm (R.thDn t x))

def PIoP (i : Fin D.R.m) (io : type_of% (R.ioP i)) : Prop :=
  ∀ t, IsIoW R.θ (R.MW i (sg0 D A)) (R.cV i) (R.ωP i t) (R.ptP i t) (Delta i) io

def PThF (i : Fin D.R.m) (t : T) (th : (R.HV i t).H →ₗ[ℂ] MMap (R.MW i (sg0 D A))) : Prop :=
  (∀ x, th x ∈ R.Wall i (sg0 D A)) ∧
    ∃ thP, Lift.IsThetaP (R.νV i t) (R.fdV i t) (fun g h f => thetaKO (R.ωP i t) h g f) (R.ptP i t) (R.ioP i)
        (LinearMap.range (R.extV i t)) thP ∧
      ∀ x (v : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ),
        th x (fun ρ => v ρ) = thP ((R.extV i t).rangeRestrict x) (PiTensorProduct.tprod ℂ v)

def PThG (i : Fin D.R.m) (t : T) (g : (R.HV i t).H →ₗ[ℂ] (R.HW i (sg0 D A)).H) : Prop :=
  ∀ x, (R.HW i (sg0 D A)).e (g x) = postOn _ (R.eWf i (sg0 D A)) (R.thF i t x)

abbrev cw_ItY : Prop :=
  ∀ k, k + 1 < D.R.m → OrZero (R.PItY k) (R.ItY k)

abbrev cw_ItX : Prop :=
  OrZero R.PItX R.ItX

abbrev cw_ioY : Prop :=
  ∀ t k, k + 1 < D.R.m → OrZero (R.PIoY t k) (R.ioY t k)

abbrev cw_ioX : Prop :=
  ∀ t, OrZero (R.PIoX t) (R.ioX t)

abbrev cw_Th : Prop :=
  ∀ t, OrZero (R.PTh t) (R.Th t)

structure IsChainW : Prop where
  ωY : R.chain_ωY
  ωX : R.chain_ωX
  vY : R.chain_vY
  vX : R.chain_vX
  ptY : R.chain_ptY
  ptX : R.chain_ptX
  ItY : R.cw_ItY
  ItX : R.cw_ItX
  ioY : R.cw_ioY
  ioX : R.cw_ioX
  Th : R.cw_Th

abbrev tw_ioP : Prop :=
  ∀ i, OrZero (R.PIoP i) (R.ioP i)

abbrev tw_thF : Prop :=
  ∀ i t, OrZero (R.PThF i t) (R.thF i t)

abbrev tw_thG : Prop :=
  ∀ i t, OrZero (R.PThG i t) (R.thG i t)

structure IsThPW : Prop where
  ωP : R.thP_ωP
  vP : R.thP_vP
  pt_theta : R.thP_pt_theta
  ioP : R.tw_ioP
  thF : R.tw_thF
  thG : R.tw_thG

abbrev ex_ItY : Prop :=
  ∀ k, k + 1 < D.R.m → ∃ y, R.PItY k y

abbrev ex_ItX : Prop :=
  ∃ y, R.PItX y

abbrev ex_ioY : Prop :=
  ∀ t k, k + 1 < D.R.m → ∃ y, R.PIoY t k y

abbrev ex_ioX : Prop :=
  ∀ t, ∃ y, R.PIoX t y

abbrev ex_Th : Prop :=
  ∀ t, ∃ y, R.PTh t y

abbrev ex_ioP : Prop :=
  ∀ i, ∃ y, R.PIoP i y

abbrev ex_thF : Prop :=
  ∀ i t, ∃ y, R.PThF i t y

abbrev ex_thG : Prop :=
  ∀ i t, ∃ y, R.PThG i t y

structure ExAt : Prop where
  ItY : R.ex_ItY
  ItX : R.ex_ItX
  ioY : R.ex_ioY
  ioX : R.ex_ioX
  Th : R.ex_Th
  ioP : R.ex_ioP
  thF : R.ex_thF
  thG : R.ex_thG

structure BaseW (F : Face D A) : Prop where
  lev : R.toLevCh.Is A.μ0
  grp : R.IsGrp F
  fam : R.IsFam
  models : R.IsModels
  chain : R.IsChainW
  thP : R.IsThPW

variable {R}

theorem chain_of_weak (h : R.IsChainW) (e : R.ExAt) : R.IsChain := ⟨h.ωY, h.ωX, h.vY, h.vX, h.ptY, h.ptX,
  fun t k hk => (h.ItY k hk).1 (e.ItY k hk) t,
  fun t => h.ItX.1 e.ItX t,
  fun t k hk => (h.ioY t k (by omega)).1 (e.ioY t k (by omega)),
  fun t => (h.ioX t).1 (e.ioX t),
  fun t => (h.Th t).1 (e.Th t)⟩

theorem thP_of_weak (h : R.IsThPW) (e : R.ExAt) : R.IsThP := ⟨h.ωP, h.vP, h.pt_theta,
  fun i t => (h.ioP i).1 (e.ioP i) t,
  fun i t x => ((h.thF i t).1 (e.thF i t)).1 x,
  fun i t => ((h.thF i t).1 (e.thF i t)).2,
  fun i t => (h.thG i t).1 (e.thG i t)⟩

end RealDat

end Weak

end Formalism.IndefR.Links

end
end
