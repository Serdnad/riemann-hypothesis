module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MidChart
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.SpectralTiesReal
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.Bundle001
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle029
public import Formalism.LocalToGlobal.GroupLattices.Joint0
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle014
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle290
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinAfMemIntUIff
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle318
import Formalism.LocalToGlobal.Columns.BaseLemmas
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle005
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle007
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
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.ReduceModChar
import Formalism.LocalToGlobal.UnitaryNorms.CharTransport
import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.HCFFromRecipA
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle004

@[expose] public section

section

noncomputable section

namespace GlobalTheory.Core.Ht2

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions _root_.Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2

attribute [local instance] GlobalTheory.Mem.Col2.starE

variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X) (u : B.Word) (a : I.ι)

abbrev ColsK : Type := MfV (Pr := B.primes X) B.wts I.Ch u

abbrev RowsK : Type := MtildeV (Pr := B.primes X) B.wts I.Ch I.sel (I.tup a) I.Ps

structure CplData where

  b : (I.idx a).β (B.R.m - 2 + 1)
  hY : YbHyp (Pr := B.primes X) (R := B.R) I.sel (I.tup a) (I.cst a) (I.idx a) u (B.R.m - 2) b
  hK : KerEquivC (Pr := B.primes X) B.wts I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) I.A u (B.R.m - 2) b hY I.Ps
  hF : ∀ j, (chF (Pr := B.primes X) B.wts I.sel (I.tup a) (I.idx a) u j).Ok

variable {I u a}

def CplData.per (c : CplData I u a) (h : I.Ok) (hX : B.fields.Ok) :
    ColsK I u →ₗ[B.fields.K] RowsK I a →ₗ[B.fields.K] B.fields.K :=
  PtilE (Pr := B.primes X) B.wts I.Ch I.sel (I.tup a) I.Ps (mtildeOk (Pr := B.primes X) B.wts I.Ch I.sel (I.tup a) hX I.Ps) u ∘ₗ
    colMu (Pr := B.primes X) B.wts I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) I.A u (B.R.m - 2) c.b c.hY I.Ps c.hK c.hF (h.idx_ok a)

variable (I u a) (l : I.Laws)

def IsCol (x : ((I.fm l u a).lat 0).V) (φ : ColsK I u) : Prop :=
  ∀ c : (I.stp u a 0).Cl, x.1 c = φ.1 ((I.stp u a 0).rep c).1.1.deco

def IsRow (F : (I.per l u a).Mt) (z : RowsK I a) : Prop :=
  ∀ p : (I.stX a).D (), F.1 () p = MvPolynomial.map B.embLL (z.1 (toRow I.sel (I.tup a) p.1.1)).1

def ColMatch (h : I.Ok) (hX : B.fields.Ok) : Prop :=
  Nonempty (CplData I u a) ∧ ∀ (c : CplData I u a) x φ F z, IsCol I u a l x φ → IsRow I u a l F z →
    (I.per l u a).PtilCol ((I.fm l u a).emb 0 x) F = B.embLL (c.per h hX φ z)

def ColMatchAll : Prop :=
  ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X) (h : I.Ok) (hX : B.fields.Ok) (l : I.Laws) (_Z : TC.Later B (I.cols l)),
    ColIn.JetsIn I → ∀ u a, ColMatch I u a l h hX

end GlobalTheory.Core.Ht2

end
end

section

noncomputable section

namespace GlobalTheory.Core.Cls.JointsStd

open NumberField IsDedekindDomain Formalism.L2.Host Formalism.L2.Host.CT Neutral.B1

section Refl

variable {E : Type} [Field E] [NumberField E]

end Refl

section Std

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2 _root_.Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem exists_vG_over {X : Fields} {Pr : Primes X} (hX : X.Ok) (hPr : Pr.Ok) (k : Fin 2) (v : HeightOneSpectrum (𝓞 X.F))
    (h : ((Pr.g k : ℕ) : 𝓞 X.F) ∈ v.asIdeal) : ∃ w ∈ Pr.vG k, w.under (𝓞 X.F) = v := by
  have := v.isPrime
  obtain ⟨⟨w, hwp, hwl⟩⟩ : Nonempty (v.asIdeal.primesOver (𝓞 X.E)) := inferInstance
  have hw : ∀ a : 𝓞 X.F, algebraMap (𝓞 X.F) (𝓞 X.E) a ∈ w ↔ a ∈ v.asIdeal := fun a => by
    rw [hwl.over]; rfl
  have hg0 : ((Pr.g k : ℕ) : 𝓞 X.E) ≠ 0 := Nat.cast_ne_zero.2 (hPr.g_prime k).ne_zero
  have hg : ((Pr.g k : ℕ) : 𝓞 X.E) ∈ w := by simpa using (hw _).2 h
  have h0 : X.conjO (Pr.piG k) ≠ 0 := right_ne_zero_of_mul (a := Pr.piG k) (by rw [hPr.piG_norm k]; exact hg0)
  have hcc : ∀ x, X.conjO (X.conjO x) = x := fun x => RingOfIntegers.ext (star_star (x : X.E))
  have hF : ∀ a : 𝓞 X.F, X.conjO (algebraMap (𝓞 X.F) (𝓞 X.E) a) = algebraMap (𝓞 X.F) (𝓞 X.E) a := fun a =>
    RingOfIntegers.ext (hX.star_F (a : X.F))
  have hg' := hg
  rw [← hPr.piG_norm k] at hg'
  rcases hwp.mem_or_mem hg' with h1 | h1
  · refine ⟨⟨w.comap X.conjO, Ideal.comap_isPrime _ _, fun e => h0 ?_⟩, (mem_divs h0 _).2 ?_, HeightOneSpectrum.ext (Ideal.ext fun a => ?_)⟩
    · exact Ideal.mem_bot.1 (e ▸ (show X.conjO (X.conjO (Pr.piG k)) ∈ w by rw [hcc]; exact h1))
    · show X.conjO (X.conjO (Pr.piG k)) ∈ w
      rw [hcc]; exact h1
    · show X.conjO (algebraMap (𝓞 X.F) (𝓞 X.E) a) ∈ w ↔ _
      rw [hF, hw]
  · exact ⟨⟨w, hwp, fun e => hg0 (Ideal.mem_bot.1 (e ▸ hg))⟩, (mem_divs h0 _).2 h1, HeightOneSpectrum.ext (Ideal.ext hw)⟩

variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X) (hOk : I.Ok) (l : I.Laws) (Z : TC.Later B (I.cols l))
include hOk

theorem piBar_std (k : Fin 2) : ∃ y : 𝓞 B.host.K,
    ((y : B.host.K) : B.host.E) = (B.fields.conjO (X.piG k) : B.host.E) ∧ y ∈ (I.C.P.pb k).asIdeal := by
  have hPr := (base_fields_primes_ok B X).2.1
  have hK : (B.fields.conjO (X.piG k) : B.host.E) ∈ B.host.K := by
    have h := HostK.conj_mem B.host (X.piG_K k)
    rw [← B.fields_star] at h
    exact h
  have hi : IsIntegral ℤ (⟨_, hK⟩ : B.host.K) :=
    (isIntegral_algebraMap_iff ).1 (B.fields.conjO (X.piG k)).2
  refine ⟨⟨_, hi⟩, rfl, ?_⟩
  have := (I.C.P.pb k).isPrime
  obtain ⟨⟨w, hwp, hwl⟩⟩ : Nonempty ((I.C.P.pb k).asIdeal.primesOver (𝓞 B.host.E)) := inferInstance
  have hg0 : ((B.host.g k : ℕ) : 𝓞 B.host.E) ≠ 0 := Nat.cast_ne_zero.2 (hPr.g_prime k).ne_zero
  have hg : ((B.host.g k : ℕ) : 𝓞 B.host.E) ∈ w := by
    have h1 := I.C.P.pb_over k
    rw [hwl.over] at h1
    simpa using (Ideal.mem_comap.1 h1)
  have h0 : B.fields.conjO (X.piG k) ≠ 0 := right_ne_zero_of_mul (a := X.piG k) (by rw [hPr.piG_norm k]; exact hg0)
  have h2 := (hOk.pibar k ⟨w, hwp, fun e => hg0 (Ideal.mem_bot.1 (e ▸ hg))⟩).2 (HeightOneSpectrum.ext hwl.over.symm)
  rw [hwl.over]
  exact (mem_divs h0 _).1 h2

theorem om_std (G : GLoc (I.rec7 l Z).host.F (I.rec7 l Z).host.E (sigD (I.rec7 l Z)) (I.rec7 l Z).host.g) (hG : I.IdG l Z G)
    (k : Fin 2) (v : HeightOneSpectrum (𝓞 B.host.F)) (h : (B.host.g k : 𝓞 B.host.F) ∈ v.asIdeal) (a n : ℕ)
    (hn : n.Coprime (B.host.g k)) (ha : a < B.R.m) :
    G.chiB k v h a (n : kv B.host.F v) = ((I.C.W.om k (ZMod.unitOfCoprime n hn) ^ (2 * (a + 1)) : ℂˣ) : ℂ) := by
  classical
  obtain ⟨hX, hPr, -⟩ := base_fields_primes_ok B X
  obtain ⟨w, hw, hv⟩ := exists_vG_over hX hPr k v h
  have hws : w ∈ (B.primes X).vGs := by
    unfold Primes.vGs
    rw [Finset.mem_union]
    fin_cases k
    exacts [Or.inl hw, Or.inr hw]
  have hg : ((B.host.g k : ℕ) : 𝓞 B.host.E) ∈ w.asIdeal := by
    rw [← hv] at h
    simpa using (Ideal.mem_comap.1 h)
  have hu : IsUnit ((n : ℕ) : 𝓞 B.fields.E ⧸ w.asIdeal) := by
    have h1 : IsCoprime ((n : ℕ) : 𝓞 B.fields.E ⧸ w.asIdeal) ((B.host.g k : ℕ) : 𝓞 B.fields.E ⧸ w.asIdeal) := hn.cast
    have h2 : ((B.host.g k : ℕ) : 𝓞 B.fields.E ⧸ w.asIdeal) = 0 := by
      rw [← map_natCast (Ideal.Quotient.mk w.asIdeal)]
      exact Ideal.Quotient.eq_zero_iff_mem.2 hg
    rwa [h2, isCoprime_zero_right] at h1
  have hn0 : ((n : ℕ) : B.host.E) ≠ 0 := by
    rintro e
    obtain rfl : n = 0 := Nat.cast_eq_zero.1 e
    have := w.isPrime
    simp at hu
  have e1 := hG.chi k v h ⟨w, hws⟩ hv ⟨a, ha⟩ n hu.unit rfl
  have e2 := (hOk.ch_tied.mu0 ⟨a, ha⟩).atg ⟨w, hws⟩ (Units.mk0 _ hn0) (n : 𝓞 B.fields.E) hu.unit (by simp) (by simp)
  have e3 := (I.C.isMu0 ⟨a, ha⟩).atg k w ((hOk.pibar k w).1 hw) n hn (Units.mk0 _ hn0) rfl
  rw [e3, Units.val_inv_eq_inv_val, Units.val_inv_eq_inv_val, map_inv₀, inv_inj] at e2
  exact e1.trans e2.symm

variable (hP : TC.Pins B X) {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : G.Inst (I.rec7 l Z) L}
  {Gl : G.LatInst (I.rec7 l Z)} {K : G.Consts} {Y : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl K Y cX}
include hP

end Std

section Local

open Formalism.L2.DIV GlobalTheory.Mem.Col2 ReciprocityTheory.Neutral.Bridge.HCFR
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem idem_comp {e : AfE F E} {P : HeightOneSpectrum (𝓞 E)} (he : e * e = e)
    (h : ∀ x : 𝓞 E, x ≠ 0 → (x ∈ P.asIdeal ↔ e * (((x : E)⁻¹) ⊗ₜ[F] (1 : FiniteAdeleRing (𝓞 F) F)) ∉ RInt F E)) :
    afIso F E e P = 1 ∧ ∀ Q, Q ≠ P → afIso F E e Q = 0 := by
  have h01 : ∀ Q, afIso F E e Q = 0 ∨ afIso F E e Q = 1 := fun Q => by
    have h1 : afIso F E e Q * afIso F E e Q = afIso F E e Q := congrArg (fun z => z Q) ((map_mul (afIso F E) e e).symm.trans (congrArg _ he))
    exact IsIdempotentElem.iff_eq_zero_or_one.1 h1
  have hv : ∀ (x : 𝓞 E) Q, afIso F E (e * (((x : E)⁻¹) ⊗ₜ[F] (1 : FiniteAdeleRing (𝓞 F) F))) Q =
      afIso F E e Q * algebraMap E (Q.adicCompletion E) (x : E)⁻¹ := fun x Q => by
    rw [map_mul, afIso_tmul_one]; rfl
  have h0 : ∀ Q, Q ≠ P → afIso F E e Q = 0 := fun Q hQ => by
    refine (h01 Q).resolve_right fun h1 => ?_
    obtain ⟨x, hx, hxP⟩ : ∃ x ∈ Q.asIdeal, x ∉ P.asIdeal := by
      by_contra hc
      push Not at hc
      exact hQ (HeightOneSpectrum.ext (Q.isMaximal.eq_of_le P.isPrime.ne_top hc))
    have hx0 : x ≠ 0 := fun e0 => hxP (e0 ▸ zero_mem _)
    have h2 := (mem_rInt_iff F E _).1 (not_not.1 ((h x hx0).not.1 hxP)) Q
    rw [hv, h1, one_mul, valued_algebraMap, map_inv₀] at h2
    have h3 := (HeightOneSpectrum.valuation_lt_one_iff_mem (K := E) Q x).2 hx
    have h4 : 0 < Q.valuation E (algebraMap (𝓞 E) E x) :=
      zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 (RingOfIntegers.coe_ne_zero_iff.2 hx0))
    exact absurd ((inv_le_one₀ h4).1 h2) (not_le.2 h3)
  refine ⟨(h01 P).resolve_left fun h1 => ?_, h0⟩
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot P.ne_bot
  refine (h x hx0).1 hx ((mem_rInt_iff F E _).2 fun Q => ?_)
  rw [hv]
  by_cases hQ : Q = P
  · subst hQ; rw [h1]; simp
  · rw [h0 Q hQ]; simp

theorem finAf_localIdele {e : AfE F E} {P : HeightOneSpectrum (𝓞 E)} (he : e * e = e)
    (h : ∀ x : 𝓞 E, x ≠ 0 → (x ∈ P.asIdeal ↔ e * (((x : E)⁻¹) ⊗ₜ[F] (1 : FiniteAdeleRing (𝓞 F) F)) ∉ RInt F E)) (k : Eˣ) :
    (finAf F E (localIdele E P (atFin P k)) : AfE F E) = 1 + e * ((k : E) ⊗ₜ[F] (1 : FiniteAdeleRing (𝓞 F) F) - 1) := by
  obtain ⟨h1, h0⟩ := idem_comp he h
  refine (afIso F E).injective (FiniteAdeleRing.ext _ fun Q => ?_)
  have e1 : afIso F E (1 + e * ((k : E) ⊗ₜ[F] (1 : FiniteAdeleRing (𝓞 F) F) - 1)) Q =
      1 + afIso F E e Q * (algebraMap E (Q.adicCompletion E) (k : E) - 1) := by
    rw [map_add (f := _), map_mul, map_sub, map_one, afIso_tmul_one]; rfl
  rw [e1, GlobalTheory.Mem.ReadTwist.afIso_finAf_apply]
  by_cases hQ : Q = P
  · subst hQ
    rw [GlobalTheory.Mem.LocTriv.ev_local_self, h1, one_mul, add_sub_cancel]
    rfl
  · rw [GlobalTheory.Mem.LocTriv.ev_local_ne hQ, h0 Q hQ, zero_mul, add_zero]

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {K : G.Consts} {Y : DivX D} {cX : ExtraC}
  {ex : Extra D L hT Gi Gl K Y cX}

attribute [local instance] Formalism.BasicNotions.Host.cmStar

end Local

end GlobalTheory.Core.Cls.JointsStd

end
end

section

set_option genSizeOfSpec false
set_option genInjectivity false

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk
open scoped TensorProduct Classical

namespace GlobalTheory.AdForm
attribute [local instance] Formalism.BasicNotions.Host.cmStar

def intVec (D : D7) (n : ℕ) : Set (Fin n → D.host.E) := {x | ∀ k, IsIntegral ℤ (x k)}

def IsFinComb {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (f₀ f : WO S T → ℂ) : Prop :=
  ∃ (n : ℕ) (c : Fin n → ℂ) (x : Fin n → WO S T), (∀ k, (x k).map (infPart D) = 0) ∧ f = ∑ k, c k • heisO ψ S T (x k) f₀

abbrev stdHom {D : D7} (S T : HSp D) : AddSubgroup (WO S T) := latO S T (intVec D S.rank) (intVec D T.rank) fun _ => True

def IsRatDatum {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (e : AE D)
    (Ξ : Matrix (Fin T.rank) (Fin S.rank) D.host.E → ℂ) (f₀ f : WO S T → ℂ) : Prop :=
  ∃ Φ : WO S T → ℂ, IsSBHalf e (stdHom S T) Φ ∧ (∀ γ, Φ (γ.map fun a => e * incA D a) = Ξ γ) ∧
    IsThetaAt ψ (symplO S T) (heisO ψ S T) e (stdHom S T) 1 f₀ Φ f

section Dat
variable {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word)

structure ColDat (Ch : ℕ → Type) where

  ch : ∀ i, Ch i

  chr : ℕ → ((AE (I.rec7 l Z))ˣ →* Circle)

  om : ∀ i, Om ((I.rec7 l Z).sp.X i) ((I.rec7 l Z).sp.X (i + 1))

  vac : ∀ i, WO ((I.rec7 l Z).sp.X i) ((I.rec7 l Z).sp.X (i + 1)) → ℂ

  w : ∀ i, WO ((I.rec7 l Z).sp.X i) ((I.rec7 l Z).sp.X (i + 1)) → ℂ

  μ : ∀ i, Measure (GA (I.rec7 l Z) ((I.rec7 l Z).sp.X i))
  fd : ∀ i, Set (GA (I.rec7 l Z) ((I.rec7 l Z).sp.X i))

  e : AE (I.rec7 l Z)

  kb : ∀ i, TC.GA B (B.R.N i)
  b0 : ∀ i, Idx I.sel (I.tup I.mu0) (I.idx I.mu0) i
  p0 : ∀ i, PtAt B.R I.sel (I.tup I.mu0) (I.cst I.mu0) u i

variable {I l Z u} {Ch : ℕ → Type} {chOf : ∀ i, ((I.rec7 l Z).mem u).C.cls i → Ch i}

namespace ColDat
variable (A : ColDat I l Z u Ch) (F : FormsTiedSym (I.rec7 l Z) u Ch chOf)
  (ψ : AddChar (AF (I.rec7 l Z).host.F) ℂ) (θ : InfFam (I.rec7 l Z))

def xi (i : ℕ) (hi : i + 1 ≤ B.R.m)
    (γ : Matrix (Fin ((I.rec7 l Z).sp.X (i + 1)).rank) (Fin ((I.rec7 l Z).sp.X i).rank) (I.rec7 l Z).host.E) : ℂ :=
  B.embLL (xiAt I.Ch I.sel (I.tup I.mu0) (I.cst I.mu0) (I.idx I.mu0) u i (A.b0 i) (A.b0 (i + 1)) (A.p0 i) (A.p0 (i + 1))
    (Matrix.toLin' (γ.reindex (finCongr (rankN (I.rec7 l Z) (i + 1) hi)) (finCongr (rankN (I.rec7 l Z) i (Nat.le_of_succ_le hi))))))

abbrev Q (i : ℕ) (hi : i ≤ B.R.m) : Chart (I.rec7 l Z) u i hi := chart F i hi (A.ch i)

structure Is : Prop where
  std : IsStdChar (I.rec7 l Z) ψ (-1)
  inf : IsInfFam θ
  chr : ∀ j : Fin B.R.m, ChrEq (A.chr ((j : ℕ) + 1)) (I.C.mu0 j)
  om : ∀ i, i < B.R.m → IsWeilDatumO ψ _ _ (A.chr (i + 1)) (A.chr (i + 1)) (A.om i)
  vac : ∀ i, i < B.R.m → IsVacO ψ θ _ _ (fun _ => 1) (fun _ => 1) (intVec _ _) (intVec _ _) (A.vac i)
  idem : IsIdemSum A.e (Formalism.L2.Col.Sall (Pr := B.primes X) I.sel (I.tup I.mu0) u)
  datum : ∀ i (hi : i + 1 ≤ B.R.m), IsRatDatum ψ _ _ A.e (A.xi i hi) (A.vac i) (A.w i)
  comb : ∀ i, i < B.R.m → IsFinComb ψ _ _ (A.vac i) (A.w i)
  haar : ∀ i, i ≤ B.R.m → (A.μ i).IsHaarMeasure ∧ IsFundamentalDomain (GQ ((I.rec7 l Z).sp.X i)) (A.fd i) (A.μ i)

  base : ∀ i, i ≤ B.R.m → TC.PtOf (A.kb i) (A.p0 i).1.1 ∧ (A.p0 i).1.1.deco.1.N = Formalism.L2.Col.stdLat B.fields.E (B.R.N i)

  chart_ne : ∀ i hi, Nonempty (A.Q F i hi).cl
  rep : ∀ i hi (c : (A.Q F i hi).cl),
    TC.PtOf ((show TC.GA B (B.R.N i) from ((A.Q F i hi).K.y c).1) * A.kb i) ((I.stp u I.mu0 i).rep ((A.Q F i hi).inc c)).1.1 ∧
      (show (I.stp u I.mu0 i).Cl from (A.Q F i hi).inc c).1 = A.b0 i ∧
      cosetIn ((I.stp u I.mu0 i).rep ((A.Q F i hi).inc c)) = cosetIn (A.p0 i)

def IsForm (i : ℕ) (hi : i ≤ B.R.m) (φ : ((I.rec7 l Z).mem u).C.cls i → ((I.rec7 l Z).mem u).C.Y i → ℂ) : Prop :=
  φ ∈ ((I.rec7 l Z).fm u).Fi i ∧ OnChart F i hi (A.ch i) φ

def Keeps : Prop :=
  ∀ i (hi : i + 1 ≤ B.R.m) φ, A.IsForm F i (Nat.le_of_succ_le hi) φ → A.IsForm F (i + 1) hi (((I.rec7 l Z).mem u).C.K i φ)

abbrev rd (i : ℕ) (hi : i ≤ B.R.m) := (A.Q F i hi).rd θ

end ColDat
end Dat

def RamAt {D : D7} (u : D.what₂.Word) (i : ℕ) (φ : (D.mem u).C.cls i → (D.mem u).C.Y i → ℂ) : Prop :=
  ∀ v c, ∑ a : ((D.mem u).A.Fv v)ˣ, (D.fm u).dilT i v a c (φ ((D.fm u).dil i v a c)) = 0

def IsEmbTop {D : D7} (z0 : Fin (D.R.N D.R.m) → D.host.E) (emb : GA D D.sp.X' →* GA D (D.sp.X D.R.m)) : Prop :=
  ∀ h, IsExt D z0 (incA D) ((mt _ h).reindex (finCongr (rankP D)) (finCongr (rankP D)))
    ((mt _ (emb h)).reindex (finCongr (rankN D _ le_rfl)) (finCongr (rankN D _ le_rfl)))

def TopForm {D : D7} {u : D.what₂.Word} {Ch : ℕ → Type} {chOf : ∀ i, (D.mem u).C.cls i → Ch i} (F : FormsTiedSym D u Ch chOf)
    {par} (M : Formalism.IndefR.Mult.DSModel D.sp.X' par) (eT : (D.mem u).P.Mt → SmT M → GA D D.sp.X' → ℂ) : Prop :=
  ∃ J : SmT M →ₗ[ℂ] (FrP D → ℂ), Function.Injective J ∧ (∀ v, J v ∈ ValC (gramC (gramP D) (embT D)) (sgT u)) ∧
    (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D D.sp.X' τ), ∀ (v : M.Vec) (w : M.sm τ), (w : M.H τ) = M.rep τ g (v τ) →
      ∀ y y' : FrP D, IsTr (Function.update (fun _ => 1) τ (g.reindex (finCongr (rankP D)) (finCongr (rankP D)))) y' y →
        J (PiTensorProduct.tprod ℂ (Function.update v τ w)) y = J (PiTensorProduct.tprod ℂ v) y') ∧
    ∀ (G : (D.mem u).P.Mt) (c : (D.fm u).clsP) (v : SmT M) (h : GA D D.sp.X'), h ∈ GfC D.sp.X' →
      finM _ (rankP D) h = (F.clsP.y c).1.1 →
      eT G v h = (Nat.card ((D.fm u).stabilizer₂ c) : ℂ) * (D.mem u).P.period (F.valP.eW.symm (Pi.single c (J v))) G

end GlobalTheory.AdForm
end
end

section

set_option genSizeOfSpec false
set_option genInjectivity false

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.L2.SG.PackageTie2 Formalism.L2.SG.SpectralTiesReal
open scoped TensorProduct

namespace GlobalTheory.Core.Rk

attribute [local instance] Formalism.BasicNotions.Host.cmStar

structure Link (D : D7) (u : D.what₂.Word) (W : Tower D) where

  P : W.Lv

  eT : (D.mem u).P.Mt →ₗ[ℂ] W.CXP P
  eT_onto : Function.Surjective eT

  jE : W.CP P 0 →ₗ⋆[ℂ] D.s.HH
  jE_onto : Function.Surjective jE

  Θ : Desc D u
  Θ_eq : ∀ F, ∃ T₀ : W.CP P 0, W.IsDn (eT F) T₀ ∧ Θ F = jE T₀

namespace Link

variable {D : D7} {u : D.what₂.Word} {W : Tower D} (L : Link D u W)


end Link

structure STrue (D : D7) (F₀ : ∀ u, Formalism.L2.Forms.Forms0 D u) extends STies D where

  hF : FinX Y
  tr : ∀ u, Formalism.L2.SG.ColDict.Transport X u (F₀ u)
  into : ∀ u, Formalism.L2.SG.ColDict.ColDictInto X (tr u) Y.hK
  bij : ∀ u, Formalism.L2.SG.ColDict.ColDictBij X (tr u) Y.hK
  lev : ∀ u, Formalism.L2.SG.ColDict.LevelMatch X (tr u) Y.hK
  colPin : ∀ (u : D.what₂.Word) (x : D.s.Cu u),
    Formalism.L2.SG.ColDict.colDict X (tr u) Y.hK (into u) (bij u) ((hI hF).eCu u x) = D.s_Cu u x
  inst : X.B.I = RationalEmbedding.inst D
  locTied : Formalism.L2.SG.Pf.LocCP.LocTied D

  pin : ∀ x : X.B.I.E, HEq (X.ιE x) x

section Bare

variable {D : D7} {F₀ : ∀ u, Formalism.L2.Forms.Forms0 D u}

end Bare

section Built

open GlobalTheory.Mem GlobalTheory.Mem.Col2

structure World {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) where
  ok : I.Ok
  pins : TC.Pins B X
  C : Formalism.L2.Forms.ColsTiedSym (I.rec7 l Z)
  std : I.StdC l Z C
  S : STrue (I.rec7 l Z) fun u => (C.forms u).to0

def TrueD (D : D7) : Prop :=
  ∃ (B : Base) (X : PreX B.toPre) (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l)), D = I.rec7 l Z ∧ Nonempty (World I l Z)

theorem TrueD.elim {Q : D7 → Prop}
    (h : ∀ (B : Base) (X : PreX B.toPre) (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l)), World I l Z → Q (I.rec7 l Z))
    {D : D7} (hD : TrueD D) : Q D := by
  obtain ⟨B, X, I, l, Z, rfl, ⟨w⟩⟩ := hD
  exact h B X I l Z w

theorem TrueD.sTies {D : D7} (hD : TrueD D) :
    ∃ S : STies D, FinX S.Y ∧ Formalism.L2.SG.Pf.LocCP.LocTied D :=
  TrueD.elim (Q := fun D => ∃ S : STies D, FinX S.Y ∧ Formalism.L2.SG.Pf.LocCP.LocTied D)
    (fun _ _ _ _ _ w => ⟨w.S.toSTies, w.S.hF, w.S.locTied⟩) hD

section Maps

variable {B : Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)}

end Maps

end Built

variable (D : D7) (u : D.what₂.Word)

end GlobalTheory.Core.Rk

end
end
