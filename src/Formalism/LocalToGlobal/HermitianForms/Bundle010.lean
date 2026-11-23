module

public import Formalism.LocalToGlobal.HermitianForms.Bundle008
public import Formalism.LocalToGlobal.HermitianColumns.Bundle002
public import Formalism.LocalToGlobal.HermitianForms.Bundle009
public import Formalism.LocalToGlobal.HermitianColumns.Bundle005
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

namespace Formalism.L2.Herm

attribute [local instance] Formalism.BasicNotions.Host.cmStar

structure TwChJointS {D : D7} {inQ : D.what₂.Tup → HeightOneSpectrum (𝓞 D.host.F) → Prop} (T : TwChTied D inQ)
    (H : HermColsCh D) where

  gOf : ∀ u μ i, T.Ch u μ i → H.Ch u i

  Uloc_off : ∀ u μ i (h1 : 1 ≤ i) (hm : i ≤ D.R.m) (β : T.Ch u μ i) (v : HeightOneSpectrum (𝓞 D.host.F)), v ∉ T.Q μ →
    (i + 1 ≠ D.R.m ∨ v ∉ Formalism.L2.Forms.badG D) →
    (T.lev u μ i h1 hm β).Uloc v = (H.lev u i h1 hm (gOf u μ i β)).Uloc v
  Lb_off : ∀ u μ i (h1 : 1 ≤ i) (hm : i ≤ D.R.m) (β : T.Ch u μ i) (v : HeightOneSpectrum (𝓞 D.host.F)), v ∉ T.Q μ →
    locL v (T.lev u μ i h1 hm β).Lb = locL v (H.lev u i h1 hm (gOf u μ i β)).Lb
  Q_off : ∀ u μ, ∀ v ∈ T.Q μ, (((D.mem u).A.T : ℕ) : 𝓞 D.host.F) ∉ v.asIdeal ∧ ∀ a, (D.host.g a : 𝓞 D.host.F) ∉ v.asIdeal

end Formalism.L2.Herm

namespace Formalism.L2.Forms

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def eYS {u : D.what₂.Word} {Ch : ℕ → Type} {chOf : ∀ i, (D.mem u).C.cls i → Ch i} (F : FormsTiedSym D u Ch chOf) (i : ℕ)
    (hi : i ≤ D.R.m) : (D.mem u).C.Y i ≃ Fr D i hi :=
  if h : i = 0 ∨ i = D.R.m then (F.val i hi h).eY else F.eYC i (by omega) (by omega)

theorem eYS_end {u : D.what₂.Word} {Ch : ℕ → Type} {chOf : ∀ i, (D.mem u).C.cls i → Ch i} (F : FormsTiedSym D u Ch chOf) (i : ℕ)
    (hi : i ≤ D.R.m) (h : i = 0 ∨ i = D.R.m) : eYS F i hi = (F.val i hi h).eY := by
  rw [eYS, dite_eq_left h]

variable {inQ : D.what₂.Tup → HeightOneSpectrum (𝓞 D.host.F) → Prop}

def twYS (T : Formalism.L2.Herm.TwChTied D inQ) {Ch : D.what₂.Word → ℕ → Type} {chOf : ∀ u i, (D.mem u).C.cls i → Ch u i}
    (F : ∀ u, FormsTiedSym D u (Ch u) (chOf u)) (u : D.what₂.Word) (μ : D.what₂.Tup) (i : ℕ) (hi : i ≤ D.R.m) :
    (D.chTw u μ).Y i ≃ Fr D i hi :=
  (T.eY u μ i hi).symm.trans (eYS (F u) i hi)



structure TwFormsTiedS (D : D7) (Tw : TwForms D) {inQ : D.what₂.Tup → HeightOneSpectrum (𝓞 D.host.F) → Prop}
    (T : Formalism.L2.Herm.TwChTied D inQ) {H : Formalism.L2.Herm.HermColsCh D} (J : Formalism.L2.Herm.TwChJointS T H)
    (F : ∀ u, FormsTiedSym D u (H.Ch u) (H.chOf u)) where

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

  chi_offC : ∀ u μ hμ i h1 (h2 : i + 1 ≤ D.R.m) β (κ : (ch u μ hμ i h1 (le_of_succ_m h2) β).lev.U)
    (κ' : ((F u).ch i h1 h2 (J.gOf u μ i β)).lev.U), κ.1 = κ'.1 →
    (∀ v ∈ T.Q μ, bc (prV (E := D.host.E) v) κ.1 = 1) →
    (ch u μ hμ i h1 (le_of_succ_m h2) β).lev.chi κ = ((F u).ch i h1 h2 (J.gOf u μ i β)).lev.chi κ'

  chi_offM : ∀ u μ hμ (h1 : 1 ≤ D.R.m) β (κ : (ch u μ hμ D.R.m h1 le_rfl β).lev.U)
    (κ' : ((F u).cls D.R.m le_rfl (Or.inr rfl)).lev.U), κ.1 = κ'.1 →
    (∀ v ∈ T.Q μ, bc (prV (E := D.host.E) v) κ.1 = 1) →
    (ch u μ hμ D.R.m h1 le_rfl β).lev.chi κ = ((F u).cls D.R.m le_rfl (Or.inr rfl)).lev.chi κ'

  chiJ : ∀ u μ (h : 1 ≤ D.R.m - 1), (T.levJ u μ h).U →* ℂˣ
  chiJ_eq : ∀ u μ hμ (h : 1 ≤ D.R.m - 1) β (κ : (T.levJ u μ h).U)
    (κ' : (ch u μ hμ (D.R.m - 1) h (Nat.sub_le _ _) β).lev.U), κ'.1 = reGL (rankN D (D.R.m - 1) (Nat.sub_le _ _)) _ κ.1 →
    (ch u μ hμ (D.R.m - 1) h (Nat.sub_le _ _) β).lev.chi κ' = chiJ u μ h κ

  chiJ_off : ∀ u μ (h : 1 ≤ D.R.m - 1) (κ : (T.levJ u μ h).U) (κ' : (F u).levJ.U),
    κ'.1 = reGL (rankN D (D.R.m - 1) (Nat.sub_le _ _)) _ κ.1 →
    (∀ v ∈ T.Q μ, bc (prV (E := D.host.E) v) κ.1 = 1) → chiJ u μ h κ = (F u).levJ.chi κ'

  val : ∀ u μ hμ i h1 hm, ValuationCompatibleChart (Tw.fm u μ) (twYS T F u μ i hm) (okQ D (T.Q μ)) (T.chOf u μ i)
    (lat := fun c => latCrd D i hm (T.lat u μ i c)) (ch u μ hμ i h1 hm)

  dil : ∀ u μ hμ i h1 hm, DilationCompatibleChart (Tw.fm u μ) (twYS T F u μ i hm) ((atT u μ).eV (F u).atT) (T.chOf u μ i)
    (lat := fun c => latCrd D i hm (T.lat u μ i c)) (ch u μ hμ i h1 hm)

  ipV : ∀ u μ i hi, IpVTieG (Tw.fm u μ) (twYS T F u μ i hi)

  norm : ∀ u μ i hi, NormTieG (Tw.fm u μ) (twYS T F u μ i hi)

  twisted_e0_at_mu0_eq_eMu0 : ∀ u x, Tw.e0 u D.what₂.mu0 x = Tw.eMu0 u 0 (Nat.zero_le _) x



structure SymmetricTwistedLevelData {Tw : TwForms D} {T : Formalism.L2.Herm.TwChTied D inQ} {H : Formalism.L2.Herm.HermColsCh D} {J : Formalism.L2.Herm.TwChJointS T H}
    {F : ∀ u, FormsTiedSym D u (H.Ch u) (H.chOf u)} (W : TwFormsTiedS D Tw T J F) where
  lv : ∀ u μ, μ ≠ D.what₂.mu0 → ∀ i, 1 ≤ i → ∀ hm : i ≤ D.R.m,
    LevelCompatibleLattices (Tw.fm u μ) (D.mem u).A.T ((W.atT u μ).res (F u).atT) i hm (fun c => latCrd D i hm (T.lat u μ i c))
  fMe : ∀ u μ hμ i h1 hm β v, (W.ch u μ hμ i h1 hm β).lev.fM (((W.atT u μ).eV (F u).atT) v).1 (((W.atT u μ).eV (F u).atT) v).2 ≃+
    (Tw.A u μ).Fv v
  fv : ∀ u μ hμ i h1 hm, FvTieG (lv u μ hμ i h1 hm) ((W.atT u μ).eV (F u).atT) (W.ch u μ hμ i h1 hm) (fMe u μ hμ i h1 hm)
  upN : ∀ u μ hμ i h1 hm, UpNatTieG (lv u μ hμ i h1 hm) (twYS T F u μ i hm) ((W.atT u μ).eV (F u).atT) (W.ch u μ hμ i h1 hm)
  dnN : ∀ u μ hμ i h1 hm, DnNatTieG (lv u μ hμ i h1 hm) (twYS T F u μ i hm) ((W.atT u μ).eV (F u).atT) (W.ch u μ hμ i h1 hm)
  bw : ∀ u μ, μ ≠ D.what₂.mu0 → ∀ i, 1 ≤ i → ∀ hm : i ≤ D.R.m,
    BwTieG (Tw.fm u μ) (D.mem u).A.T ((W.atT u μ).res (F u).atT) (twYS T F u μ i hm) (fun c => latCrd D i hm (T.lat u μ i c))

structure TwLvSameS {Tw : TwForms D} {T : Formalism.L2.Herm.TwChTied D inQ} {H : Formalism.L2.Herm.HermColsCh D} {J : Formalism.L2.Herm.TwChJointS T H}
    {F : ∀ u, FormsTiedSym D u (H.Ch u) (H.chOf u)} (W : TwFormsTiedS D Tw T J F) where
  step0 : ∀ u μ, LvSame (W.atT u μ) 0 (T.eCls0 u μ) (T.eY u μ 0 (Nat.zero_le _)) (Tw.e0 u μ)
  mu0 : ∀ u i (hi : i ≤ D.R.m), LvSame (W.atT u D.what₂.mu0) i (Formalism.L2.Herm.clsCast D u i) (Formalism.L2.Herm.yCast D u i) (Tw.eMu0 u i hi)

end Formalism.L2.Forms

end
end

section

noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain Matrix Formalism.UG
open scoped TensorProduct

namespace Formalism.L2.Forms

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {inQ : D.what₂.Tup → HeightOneSpectrum (𝓞 D.host.F) → Prop}

def redJS {Ch : D.what₂.Word → ℕ → Type} {chOf : ∀ u i, (D.mem u).C.cls i → Ch u i} (F : ∀ u, FormsTiedSym D u (Ch u) (chOf u))
    (u : D.what₂.Word) (a : Fin 2) (v : HeightOneSpectrum (𝓞 D.host.F))
    (hv : (D.host.g a : 𝓞 D.host.F) ∈ v.asIdeal)
    (x : GL (Fin (D.sp.X (D.R.m - 1)).rank) (D.host.E ⊗[D.host.F] v.adicCompletion D.host.F)) :
    Matrix (Fin (D.R.N (D.R.m - 1))) (Fin (D.R.N (D.R.m - 1))) (kv D.host.F v) :=
  redM D.host.F v ((F u).gl.mat a v hv ((F u).glevJ.fr a v hv)
    (reGL (rankN D (D.R.m - 1) (Nat.sub_le _ _)) _ x))



structure SymmetricTwistedJointForms (T : Formalism.L2.Herm.TwChTied D inQ) {Ch : D.what₂.Word → ℕ → Type} {chOf : ∀ u i, (D.mem u).C.cls i → Ch u i}
    (F : ∀ u, FormsTiedSym D u (Ch u) (chOf u)) where

  J_g : ∀ u μ (h : 1 ≤ D.R.m - 1) (a : Fin 2) (v : HeightOneSpectrum (𝓞 D.host.F)) (hv : (D.host.g a : 𝓞 D.host.F) ∈ v.asIdeal),
    ∀ x ∈ levelVL D.sp.cm.sig (D.sp.X (D.R.m - 1)).gram v (T.levJ u μ h).Lb,
      x ∈ (T.levJ u μ h).Uloc v ↔ ∃ M ∈ HSym D (D.R.N (D.R.m - 1)) false v,
        (M : Matrix (Fin (D.R.N (D.R.m - 1))) (Fin (D.R.N (D.R.m - 1))) (kv D.host.F v)) = redJS F u a v hv x

  J_off : ∀ u μ (h : 1 ≤ D.R.m - 1) (v : HeightOneSpectrum (𝓞 D.host.F)), v ∉ T.Q μ → v ∉ badG D →
    ((T.levJ u μ h).Uloc v).map (reGL (rankN D (D.R.m - 1) (Nat.sub_le _ _)) _).toMonoidHom =
      (F u).levJ.Uloc v

  yG : ∀ u μ (h : 1 ≤ D.R.m - 1), T.Yb u μ h → ∀ (a : Fin 2) (v : HeightOneSpectrum (𝓞 D.host.F)),
    (D.host.g a : 𝓞 D.host.F) ∈ v.asIdeal → Fin (D.R.N (D.R.m - 1)) → kv D.host.F v
  yG_smul : ∀ u μ h (κ : (T.levJ u μ h).U) y a v hv,
    yG u μ h (κ • y) a v hv = redJS F u a v hv (bc (prV (E := D.host.E) v) κ.1) *ᵥ yG u μ h y a v hv

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

def chM {D : D7} (H : Formalism.L2.Herm.HermColsCh D) (u : D.what₂.Word) : H.Ch u D.R.m :=
  @default _ (H.Ch_m u).some.toInhabited

theorem chOf_m {D : D7} (H : Formalism.L2.Herm.HermColsCh D) (u : D.what₂.Word) (c : (D.mem u).C.cls D.R.m) :
    H.chOf u D.R.m c = chM H u :=
  (H.Ch_m u).some.uniq _

theorem one_le_m (R : Ranks) : 1 ≤ R.m := by
  have h2 := R.two_le_m
  omega



structure ColsTiedSym (D : D7) where
  herm : Formalism.L2.Herm.ColsHermS D
  forms : ∀ u : D.what₂.Word, FormsTiedSym D u (herm.base.Ch u) (herm.base.chOf u)

  eV : ∀ u, (forms u).atT.eV = herm.base.vT u
  piU : ∀ u, (forms u).atT.piU = (herm.atT u).piU
  res : ∀ u, (forms u).atT.res = (herm.atT u).res

  car0 : ∀ u, SameCar (rank_eq_first_level D.R) (herm.base.lev0 u).Lb ((forms u).cls 0 (Nat.zero_le _) (Or.inl rfl)).lev.Lb
    (herm.base.lev0 u).Uloc ((forms u).cls 0 (Nat.zero_le _) (Or.inl rfl)).lev.Uloc
    (herm.base.lev0 u).U ((forms u).cls 0 (Nat.zero_le _) (Or.inl rfl)).lev.U
    (fun c => ((herm.base.lev0 u).y c).1) (fun c => (((forms u).cls 0 (Nat.zero_le _) (Or.inl rfl)).y c).1)
    (fun c s => ((herm.base.lev0 u).stabI c s).1) (fun c s => (((forms u).cls 0 (Nat.zero_le _) (Or.inl rfl)).stabI c s).1)

  carC : ∀ u i (h1 : 1 ≤ i) (h2 : i + 1 ≤ D.R.m) (β : herm.base.Ch u i),
    SameCar (rankN D i (le_of_succ_m h2)) (herm.base.lev u i h1 (le_of_succ_m h2) β).Lb ((forms u).ch i h1 h2 β).lev.Lb
      (herm.base.lev u i h1 (le_of_succ_m h2) β).Uloc ((forms u).ch i h1 h2 β).lev.Uloc
      (herm.base.lev u i h1 (le_of_succ_m h2) β).U ((forms u).ch i h1 h2 β).lev.U
      (fun c => ((herm.base.cls u i h1 (le_of_succ_m h2) β).y c).1) (fun c => (((forms u).ch i h1 h2 β).y c).1)
      (fun c s => ((herm.base.cls u i h1 (le_of_succ_m h2) β).stabI c s).1) (fun c s => (((forms u).ch i h1 h2 β).stabI c s).1)

  carM : ∀ u, SameCar (rankN D D.R.m le_rfl) (herm.base.lev u D.R.m (one_le_m D.R) le_rfl (chM herm.base u)).Lb
      ((forms u).cls D.R.m le_rfl (Or.inr rfl)).lev.Lb
      (herm.base.lev u D.R.m (one_le_m D.R) le_rfl (chM herm.base u)).Uloc ((forms u).cls D.R.m le_rfl (Or.inr rfl)).lev.Uloc
      (herm.base.lev u D.R.m (one_le_m D.R) le_rfl (chM herm.base u)).U ((forms u).cls D.R.m le_rfl (Or.inr rfl)).lev.U
      (fun c => ((herm.base.cls u D.R.m (one_le_m D.R) le_rfl (chM herm.base u)).y ⟨c, chOf_m herm.base u c⟩).1)
      (fun c => (((forms u).cls D.R.m le_rfl (Or.inr rfl)).y c).1)
      (fun c s => ((herm.base.cls u D.R.m (one_le_m D.R) le_rfl (chM herm.base u)).stabI ⟨c, chOf_m herm.base u c⟩ s).1)
      (fun c s => (((forms u).cls D.R.m le_rfl (Or.inr rfl)).stabI c s).1)

  carP : ∀ u, SameCar (rankP D) (Formalism.L2.Herm.crdLat D.sp.X' D.sp.X'.L0) (forms u).clsP.lev.Lb
    (herm.atT u).levP.Uloc (forms u).clsP.lev.Uloc (herm.atT u).levP.U (forms u).clsP.lev.U
    (fun c => ((herm.atT u).clsP.y c).1) (fun c => ((forms u).clsP.y c).1)
    (fun c s => ((herm.atT u).clsP.stabI c s).1) (fun c s => ((forms u).clsP.stabI c s).1)
  lattice₂ : ∀ u c, (forms u).clsP.lat c = ((herm.atT u).lattice₂ c).map
    ((crdP D : D.sp.X'.V →ₗ[D.host.E] (Fin (D.R.N D.R.m - 1) → D.host.E)).restrictScalars (𝓞 D.host.E))

  pr : ∀ u (i : ℕ) (hi : i ≤ D.R.m) v c (z : Formalism.L2.Herm.Ld D u i c) (z' : Ld D u i hi c),
    z'.1 = crdN D i hi z.1 → ((forms u).lv i hi).pr v c z' = (herm.atT u).pr i v c z
  prk : ∀ u (i : ℕ) (hi : i ≤ D.R.m) v c (z : Formalism.L2.Herm.Lk D u ((herm.atT u).Pv v) i c) (z' : Lk (forms u).atT i hi v c),
    z'.1 = crdN D i hi z.1 → ((forms u).lv i hi).prk v c z' = (herm.atT u).prk i v c z
  prC : ∀ u (i : ℕ) (h1 : 1 ≤ i) (h2 : i + 1 ≤ D.R.m) v c (z : Formalism.L2.Herm.Ld D u i c)
    (z' : LdG D i (le_of_succ_m h2) (clsCrd D u i (le_of_succ_m h2) c)),
    z'.1 = crdN D i (le_of_succ_m h2) z.1 → ((forms u).lvC i h1 h2).pr v c z' = (herm.atT u).pr i v c z

  z0 : ∀ u, (forms u).til.z0 = crdN D D.R.m le_rfl (herm.atT u).z0
  ga : ∀ u c, ((forms u).til.ga c).1 = reGL (rankN D D.R.m le_rfl) _
    (Formalism.L2.Herm.toGLb (D.sp.X D.R.m).frame ((herm.atT u).tilG c).1)

  sp : ∀ u, (forms u).gl.sp = (herm.base.lev0 u).splitG
  piG : ∀ u, (forms u).gl.piG = (herm.levelZeroCompatibility u).piG
  fr0 : ∀ u i v h, (forms u).glev0.fr i v h = reGL (rank_eq_first_level D.R) _ ((herm.base.lev0 u).frG i v h)
  gl_const : ∀ u u', (forms u).gl = (forms u').gl

  chi : CharacterCompatible (forms D.u₀).gl D.R.m

  frame_level_zero_const : ∀ u u', (forms u).glev0.fr = (forms u').glev0.fr
  frP_const : ∀ u u', (forms u).glevP.fr = (forms u').glevP.fr


end Formalism.L2.Forms

end
end
