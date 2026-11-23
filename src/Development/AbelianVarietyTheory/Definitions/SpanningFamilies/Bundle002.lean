module

public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsStabForm
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsSystem
public import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.LevelStructureProperties
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open AlgebraicGeometry CategoryTheory NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj GlobalTheory.Dict
open scoped Classical

namespace GlobalTheory.ClsVal

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r g q0 n : ℕ} {H : Host E} {Dw : Datum H}
  {l : Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l}

def clsSum (σ : c.F →+* ℂ) (X : Data E r) (hr : X.p0 + q0 = r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ)
    (idx : Fin g ≃ X.Ψ × Fin r) (eL : LtN Dw n ≃ Harm.Var X.Ψ q0 X.p0 (Fin n)) {l₂ : Geo.Tor.Level H} {Cl : Type}
    [Fintype Cl] (w : Cl → (Fin n → LevQ Dw l₂) → c.F) (La : Cl → GenLat E n) (Nc gam : Cl → ℕ) (vol : c.F)
    (ep : Cl → c.F) (P : Cl → MvPolynomial (LtN Dw n) c.F) (L : Lt E r) (v : TF n g)
    (Y : Cl → (Fin n → LevQ Dw l₂) → Matrix (Fin n) (Fin r) E) (x : Frame X.Ψ r) : ℂ :=
  ∑ k, σ (vol * ((gam k : c.F))⁻¹ * ep k * ((((La k).mIdx (Nc k) r : c.F))⁻¹ *
      ((Nat.card (Fin n → LevQ Dw l₂) : c.F))⁻¹ * ((La k).zCard (Nc k) r : c.F))) *
    thP X hr bas idx (gphi X bas (H.w0 : E) (La k).La L v (fun q => σ (w k q)) (Y k))
      (MvPolynomial.rename eL (MvPolynomial.map σ (P k))) x

def CvIs (d : DeltaDat Xo c n) [Algebra d.c₂.F ℂ] (X : Data E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ)
    (idx : Fin g ≃ X.Ψ × Fin r) (e : Fin g ≃ Lt1 Dw) (L : Lt E r) (cv : (Dw.La →ₗ[𝓞 E] (Fin r → E)) → ℂ) : Prop :=
  ∀ x ∈ X.dom, ∀ (y₂ : FrPt d.Xo₂ d.c₂ ℂ) (A : AnFib X bas idx e x L y₂) (mk : Dw.La →ₗ[𝓞 E] (Fin r → E)),
    IsMark d.l₂ L mk → A.Marked mk → evR d.Xo₂ d.c₂ d.cδ y₂ = cv mk

def DatEq (d : DeltaDat Xo c n) (ψ : (LaI Xo c d ≃ₗ[𝓞 E] LaI Xo c d) →* c.Fˣ)
    (w : (Fin n → LevQ Dw d.l₂) → c.F) : Prop :=
  ∀ (s : Sim Dw), s.InGam l d.l₂ → ∀ (kI : LaI Xo c d ≃ₗ[𝓞 E] LaI Xo c d) (σq : LevQ Dw d.l₂ ≃ LevQ Dw d.l₂),
    (∀ a : Dw.La, (Submodule.Quotient.mk (s.f d.l₂.M a) : LaI Xo c d) = kI (Submodule.Quotient.mk a)) →
    (∀ a : Dw.La, σq (Submodule.Quotient.mk a) = Submodule.Quotient.mk (s.f d.l₂.M a)) →
    ∀ q, w (fun b => σq.symm (q b)) = (((ψ kI)⁻¹ : c.Fˣ) : c.F) * w q

def LatsOK (M : ℕ) {Cl : Type} (La : Cl → GenLat E n) (Nc : Cl → ℕ) : Prop :=
  ∀ k, (La k).Unimod ∧ (La k).TrivAt M ∧ (La k).LevOK (Nc k) M

end

end GlobalTheory.ClsVal
end

section

open Matrix Complex NumberField MeasureTheory
open scoped ComplexConjugate
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr GlobalTheory.SW

namespace GlobalTheory.Ker

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r g : ℕ} (X : Data E r)
  (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) {n : ℕ}

abbrev WR (X : Data E r) (n : ℕ) : Type := X.Ψ → Fin n → Fin r → ℂ

def embR (y : Matrix (Fin n) (Fin r) E) : WR X n := fun τ k a => τ.1 (y k a)

def zR (x : Frame X.Ψ r) (v : WR X n) : Fin n → Fin g → ℂ := fun k i =>
  if ((idx i).2 : ℕ) < X.p0 then
    hermC (idx i).1.1 X.Gm (FD.col (mat x (idx i).1) (idx i).2) (v (idx i).1 k)
  else ((mat x (idx i).1)⁻¹ *ᵥ v (idx i).1 k) (idx i).2

def EFR (v v' : WR X n) : ℝ :=
  ∑ τ : X.Ψ, ∑ k, 2 * (τ.1 (-(X.κ0 / 2)) * hermC τ.1 X.Gm (v τ k) (v' τ k)).re

def gaussR (x : Frame X.Ψ r) (z : Fin n → Fin g → ℂ) : ℂ :=
  cexp (-(Real.pi / 2 * ∑ k, GlobalTheory.Dict.hx X bas idx x (z k) (z k)))

def thR (φ : TF n g) (x : Frame X.Ψ r) (v : WR X n) : ℂ :=
  gaussR X bas idx x (zR X idx x v) * thA X bas idx φ x (zR X idx x v)

def latR (n N : ℕ) : AddSubgroup (WR X n) :=
  AddSubgroup.closure {v | ∃ y : Matrix (Fin n) (Fin r) E, (∀ k, y k ∈ X.Λ) ∧ v = N • embR X y}

def IsONFr (x : Frame X.Ψ r) : Prop := ∀ τ : X.Ψ, gram τ.1 X.Gm (mat x τ) = sgnM X

def IdemTwo (w : E) : Prop := ∃ b : E, IsIntegral ℤ b ∧ w * cc w = 2 * b

theorem zR_embR (x : Frame X.Ψ r) (y : Matrix (Fin n) (Fin r) E) (k : Fin n) :
    zR X idx x (embR X y) k = GlobalTheory.Dict.pv X idx x (y k) := rfl

end

end GlobalTheory.Ker
end

section

open NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open GlobalTheory.SW.Lev
open Formalism.L2.Pj
open scoped Classical

namespace GlobalTheory.Dict.TieModel

noncomputable section

variable {E : Type} [Field E] [NumberField E]

theorem exists_gen_one {𝔪 : Ideal (𝓞 E)} (h0 : 𝔪 ≠ ⊥) (A : Submodule (𝓞 E) E) (hA : A.FG) :
    ∃ p ∈ A, A ≤ Submodule.span (𝓞 E) {p} ⊔ 𝔪 • A := by
  by_cases hb : A = ⊥
  · exact ⟨0, zero_mem _, by simp [hb]⟩
  obtain ⟨d, hd, hint⟩ := FractionalIdeal.isFractional_of_fg (S := nonZeroDivisors (𝓞 E)) hA
  have hd0 : (d : E) ≠ 0 := by simpa using nonZeroDivisors.ne_zero hd
  let f : 𝓞 E →ₗ[𝓞 E] E := LinearMap.toSpanSingleton (𝓞 E) E (d : E)⁻¹
  have hf (a : 𝓞 E) : f a = (a : E) * (d : E)⁻¹ := rfl
  let I : Ideal (𝓞 E) := A.comap f
  have hI : Submodule.map f I = A := by
    refine Submodule.map_comap_eq_self fun x hx => ?_
    obtain ⟨a, ha⟩ := hint x hx
    refine ⟨a, ?_⟩
    have : (a : E) = (d : E) * x := ha
    rw [hf, this]; field_simp
  have hI0 : I ≠ ⊥ := fun h => hb (by rw [← hI, h, Submodule.map_bot])
  obtain ⟨p, hp⟩ := IsDedekindDomain.exists_sup_span_eq (I := 𝔪 * I) (J := I) Ideal.mul_le_right
    (mul_ne_zero h0 hI0)
  have hpI : p ∈ I := hp ▸ Submodule.mem_sup_right (Ideal.mem_span_singleton_self p)
  refine ⟨f p, hpI, ?_⟩
  conv_lhs => rw [← hI, ← hp]
  rw [Submodule.map_sup, sup_comm]
  refine sup_le_sup ?_ ?_
  · rw [Ideal.span, Submodule.map_span, Set.image_singleton]
  · rw [← smul_eq_mul, Submodule.map_smul'', hI]

theorem exists_gens {𝔪 : Ideal (𝓞 E)} (h0 : 𝔪 ≠ ⊥) : ∀ (r : ℕ) (L : Submodule (𝓞 E) (Fin r → E)), L.FG →
    ∃ β : Fin r → Fin r → E, (∀ i, β i ∈ L) ∧ L ≤ Submodule.span (𝓞 E) (Set.range β) ⊔ 𝔪 • L := by
  intro r
  induction r with
  | zero => exact fun L _ => ⟨fun i => i.elim0, fun i => i.elim0, fun v _ => by
      rw [Subsingleton.elim v 0]; exact zero_mem _⟩
  | succ r ih =>
    intro L hL
    let π : (Fin (r + 1) → E) →ₗ[𝓞 E] E := LinearMap.proj 0
    let ι : (Fin r → E) →ₗ[𝓞 E] (Fin (r + 1) → E) := LinearMap.vecCons 0 LinearMap.id
    have hι : Function.Injective ι := fun a b h => by
      simpa [ι] using h
    obtain ⟨_, ⟨b, hb, rfl⟩, hgen⟩ := exists_gen_one h0 (L.map π) (hL.map π)
    have hfg : (L.comap ι).FG :=
      Submodule.fg_of_fg_map_injective ι hι (Submodule.FG.of_le hL (Submodule.map_comap_le _ _))
    obtain ⟨β, hβ, hsp⟩ := ih _ hfg
    refine ⟨Fin.cons b fun i => ι (β i), fun i => Fin.cases hb (fun i => hβ i) i, fun v hv => ?_⟩
    have h1 := hgen ⟨v, hv, rfl⟩
    rw [← Set.image_singleton, ← Submodule.map_span, ← Submodule.map_smul'', ← Submodule.map_sup] at h1
    obtain ⟨w, hw, e⟩ := h1
    have hwL : w ∈ L := (sup_le (Submodule.span_le.2 (by simpa using hb)) Submodule.smul_le_right :
      _ ≤ L) hw
    have e2 : v - w = ι (Fin.tail (v - w)) := by
      funext j
      refine Fin.cases ?_ (fun j => ?_) j
      · have : w 0 = v 0 := e
        simp [ι, this]
      · simp [ι, Fin.tail]
    have h2 : Fin.tail (v - w) ∈ L.comap ι := by
      rw [Submodule.mem_comap, ← e2]; exact sub_mem hv hwL
    have h3 := Submodule.mem_map_of_mem (f := ι) (hsp h2)
    rw [← e2, Submodule.map_sup, Submodule.map_smul'', Submodule.map_span] at h3
    rw [← sub_add_cancel v w]
    refine add_mem (SetLike.le_def.1 (sup_le_sup (Submodule.span_mono ?_)
      (Submodule.smul_mono le_rfl (Submodule.map_comap_le _ _))) h3)
      (SetLike.le_def.1 (sup_le_sup_right (Submodule.span_mono ?_) _) hw)
    · rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
      exact ⟨i.succ, rfl⟩
    · rintro _ rfl
      exact ⟨0, rfl⟩

variable [IsCMField E] {r n : ℕ} {X : Data E r}

theorem cong_mono {𝔞 𝔟 : Ideal (𝓞 E)} (h : 𝔞 ≤ 𝔟) {u v : Fin r → E} (H : Cong X 𝔞 u v) : Cong X 𝔟 u v := by
  obtain ⟨s, hs, H⟩ := H
  obtain ⟨a, m, hm, e⟩ := cop_iff.1 hs
  exact ⟨s, cop_iff.2 ⟨a, m, h hm, e⟩, Submodule.smul_mono h le_rfl H⟩

variable {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l}

theorem m_mem (l : Geo.Tor.Level H) : (l.M : 𝓞 E) ∈ Mfr l :=
  (l.prod.ge.trans Ideal.mul_le_right) (Ideal.mem_span_singleton_self _)



end

end GlobalTheory.Dict.TieModel
end
