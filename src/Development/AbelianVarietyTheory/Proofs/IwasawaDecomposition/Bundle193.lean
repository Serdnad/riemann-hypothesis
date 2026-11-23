module

public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.RedPEqZeroOfDiv
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle076
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.UnipotentCharacterArgumentMulStabilizer
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevQFiniteIndexAndRoot
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle189
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowTypeMulOnSymmetricLevelAtTypePrime
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PosPartUnitaryMul
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallyExistsFiniteSubsetNonzeroLocus
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle146
public import Development.AbelianVarietyTheory.Definitions.Divisors.LineBundleGlobalSectionsDimCongrPicardClass
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.SumNegOnePowFinrankEqZero
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle180
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle184
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle186
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle187
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle188
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelGroupReductionStepZeroTypePrime
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GlESymmApply
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle185
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHarishChandraTypeDualWeylModuleFockNorm
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.GlobalTheory.GL6.Statement

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col
open Classical

noncomputable section

namespace GlobalTheory.Mem.Col2.IdxEx.LocMatch

theorem cbe_iff {k : Type} [CommRing k] {n c : ℕ} (J : Subgroup ((Fin (n + c) → k) ≃ₗ[k] (Fin (n + c) → k)))
    {r h' κ s : (Fin (n + c) → k) ≃ₗ[k] (Fin (n + c) → k)} (hr : r ∈ Loc.R1 k n c) (hκ : κ ∈ J) :
    s ∈ Loc.Cbe J (r * h' * κ) ↔ r⁻¹ * s * r ∈ Loc.Cbe J h' := by
  constructor
  · rintro ⟨hs1, hs2⟩
    refine ⟨(Loc.R1 k n c).mul_mem ((Loc.R1 k n c).mul_mem ((Loc.R1 k n c).inv_mem hr) hs1) hr, ?_⟩
    have h2 : (r * h' * κ)⁻¹ * s * (r * h' * κ)⁻¹⁻¹ ∈ J := hs2
    show h'⁻¹ * (r⁻¹ * s * r) * h'⁻¹⁻¹ ∈ J
    have e : h'⁻¹ * (r⁻¹ * s * r) * h'⁻¹⁻¹ = κ * ((r * h' * κ)⁻¹ * s * (r * h' * κ)⁻¹⁻¹) * κ⁻¹ := by group
    rw [e]
    exact mul_mem (mul_mem hκ h2) (inv_mem hκ)
  · rintro ⟨hs1, hs2⟩
    have hs1' : s ∈ Loc.R1 k n c := by
      have := (Loc.R1 k n c).mul_mem ((Loc.R1 k n c).mul_mem hr hs1) ((Loc.R1 k n c).inv_mem hr)
      rwa [show r * (r⁻¹ * s * r) * r⁻¹ = s by group] at this
    refine ⟨hs1', ?_⟩
    have h2 : h'⁻¹ * (r⁻¹ * s * r) * h'⁻¹⁻¹ ∈ J := hs2
    show (r * h' * κ)⁻¹ * s * (r * h' * κ)⁻¹⁻¹ ∈ J
    have e : (r * h' * κ)⁻¹ * s * (r * h' * κ)⁻¹⁻¹ = κ⁻¹ * (h'⁻¹ * (r⁻¹ * s * r) * h'⁻¹⁻¹) * κ := by group
    rw [e]
    exact mul_mem (mul_mem (inv_mem hκ) h2) hκ

theorem red_conj {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} {P : HeightOneSpectrum (𝓞 E)}
    (δ : GLint E n P) {g : Sp E n ≃ₗ[E] Sp E n} (hg : g ∈ GLint E n P) {A : GL (Fin n) (𝓞 E ⧸ P.asIdeal)}
    (hA : ∀ y ∈ stdAt E n P, redV P (g y) = A.1.mulVec (redV P y)) :
    ∀ y ∈ stdAt E n P, redV P ((δ.1 * g * δ.1⁻¹) y) =
      (GlobalTheory.TopStep.redGL n P δ * A * (GlobalTheory.TopStep.redGL n P δ)⁻¹).1.mulVec (redV P y) := by
  intro y hy
  have h1 : δ.1⁻¹ y ∈ stdAt E n P := ((δ⁻¹).2 y).2 hy
  have h2 : g (δ.1⁻¹ y) ∈ stdAt E n P := (hg _).2 h1
  show redV P (δ.1 (g (δ.1⁻¹ y))) = _
  rw [GlobalTheory.TopStep.redV_redGL δ h2, hA _ h1]
  have h3 := GlobalTheory.TopStep.redV_redGL δ⁻¹ hy
  have e : (δ⁻¹).1 y = δ.1⁻¹ y := rfl
  rw [e] at h3
  rw [h3, map_inv, Units.val_mul, Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]

end GlobalTheory.Mem.Col2.IdxEx.LocMatch

namespace GlobalTheory.Mem.Col2.IdxEx.LocMatch

theorem inX_mem_lamYat_iff {X : Fields} {Pr : Primes X} {R : Ranks} (j : ℕ) {P : HeightOneSpectrum (𝓞 X.E)}
    (hP : P ∈ Pr.vGs) (x : Sp X.E (R.N j)) :
    Loc.inX X.E (R.N j) (cOf R j) x ∈ lamYat (Pr := Pr) (R := R) j P ↔ x ∈ stdAt X.E (R.N j) P := by
  unfold lamYat
  rw [if_pos hP]
  exact ⟨fun hx => by simpa only [GlobalTheory.CongLevel.resX_inX] using GlobalTheory.CongLevel.resX_mem P _ _ _ _ hx,
    GlobalTheory.CongLevel.inX_mem_lamY P _ _ _ x⟩

theorem lamRow_tup {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m) {S : Set ℕ}
    (mu mu' : Tup X.F X.E X.K S) (j : ℕ) {P : HeightOneSpectrum (𝓞 X.E)} (hP : P ∈ Pr.vGs)
    (f : HomE X.E (R.N j + cOf R j) (R.N j + cOf R j)) :
    lamRow Ch mu true j P f = lamRow Ch mu' true j P f := by
  unfold lamRow
  simp only [if_pos hP, if_true]

end GlobalTheory.Mem.Col2.IdxEx.LocMatch

namespace GlobalTheory.Mem.Col2.IdxEx.LocMatch

theorem loc_match : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu mu' : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (cst' : LocCst X (rowSG Pr sel mu')) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (L' : ChIdx X Pr R (QE sel (mu' : Chr X.F X.E X.K))) (G : ChGlob X R.m) (m2 : ℕ), X.Ok → Pr.Ok → Ch.Ok → cst.sharp = true → cst'.sharp = true → L.Ok Ch sel mu cst G m2 → L'.Ok Ch sel mu' cst' G m2 → ∀ (j : ℕ), j ≤ m2 + 1 → ∀ (b : L.β j) (b' : L'.β j) (w : {w // w ∈ Pr.vGs}) (r κ : AutY X R j), r ∈ Loc.R1 X.E (R.N j) (cOf R j) → κ ∈ Jat (Pr := Pr) true j w.1 → L.h j b ⟨w.1, Finset.mem_union_left _ w.2⟩ = r * L'.h j b' ⟨w.1, Finset.mem_union_left _ w.2⟩ * κ → ∃ x : GL (Fin (R.N j)) (𝓞 X.E ⧸ w.1.asIdeal), (r = 1 → x = 1) ∧ (∀ hbar : GL (Fin (R.N j)) (𝓞 X.E ⧸ w.1.asIdeal), hbar ∈ (L.levG j b w).H ↔ x * hbar * x⁻¹ ∈ (L'.levG j b' w).H) ∧ ∀ (hbar : ↥(L.levG j b w).H) (hbar' : ↥(L'.levG j b' w).H), hbar'.1 = x * hbar.1 * x⁻¹ → (L.levG j b w).lam hbar = (L'.levG j b' w).lam hbar' := by
  intro X Pr R Ch sel S mu mu' cst cst' L L' G m2 _ _ _ hs hs' hok hok' j hj b b' w r κ hr hκ he
  have hP : w.1 ∈ Pr.vGs := w.2
  have hjm : j < R.m := by rw [hok.hm]; omega
  have hG := hok.grpG j b w
  have hG' := hok'.grpG j b' w
  have hC := hok.chrG j b w
  have hC' := hok'.chrG j b' w
  have hint := hok.int j b ⟨w.1, Finset.mem_union_left _ w.2⟩
  have hint' := hok'.int j b' ⟨w.1, Finset.mem_union_left _ w.2⟩
  have hst := hok.stabG j b ⟨w.1, Finset.mem_union_left _ w.2⟩ hP
  have hst' := hok'.stabG j b' ⟨w.1, Finset.mem_union_left _ w.2⟩ hP
  have hpsi := fun a ha => hok.psi0 ⟨w.1, Finset.mem_union_left _ w.2⟩ a hP ha
  have hpsi' := fun a ha => hok'.psi0 ⟨w.1, Finset.mem_union_left _ w.2⟩ a hP ha
  rw [hs] at hG hC hint
  rw [hs'] at hG' hC' hint'
  unfold chiInv at hC hC'
  rw [hs] at hC
  rw [hs'] at hC'
  generalize L.h j b ⟨w.1, Finset.mem_union_left _ w.2⟩ = h at hG hC hint hst he
  generalize L'.h j b' ⟨w.1, Finset.mem_union_left _ w.2⟩ = h' at hG' hC' hint' hst' he
  subst he

  have hκs := jat_le_stab_lamY true j w.1 hP κ hκ
  have hrs : r ∈ stabL X.E _ (lamYat (Pr := Pr) (R := R) j w.1) := by
    have := mul_mem (mul_mem hst (inv_mem hκs)) (inv_mem hst')
    rwa [show r * h' * κ * κ⁻¹ * h'⁻¹ = r by group] at this
  obtain ⟨γ, hγ⟩ := GlobalTheory.QNormal.exists_res hr
  have hγint : γ ∈ GLint X.E (R.N j) w.1 := by
    intro y
    rw [← inX_mem_lamYat_iff (Pr := Pr) j hP, ← inX_mem_lamYat_iff (Pr := Pr) j hP, ← hγ y]
    exact hrs _
  set γg : GLint X.E (R.N j) w.1 := ⟨γ, hγint⟩ with hγg
  refine ⟨GlobalTheory.TopStep.redGL (R.N j) w.1 γg⁻¹, ?_, ?_, ?_⟩
  · intro h1
    subst h1
    have e : γ = 1 := by
      refine LinearEquiv.ext fun y => GlobalTheory.QNormal.inX_injective (c := cOf R j) ?_
      rw [← hγ y]
      rfl
    have e2 : γg = 1 := Subtype.ext e
    rw [e2, inv_one, map_one]
  · intro hbar
    rw [hG, hG']
    constructor
    · rintro ⟨g, ⟨r₁, hr₁, hres⟩, hred⟩
      refine ⟨γ⁻¹ * g * γ, ⟨r⁻¹ * r₁ * r, (cbe_iff _ hr hκ).1 hr₁, GlobalTheory.Proof.level_eq_parahoric_category.conj_res hγ hres⟩, ?_⟩
      intro y hy
      exact red_conj γg⁻¹ (hint ⟨r₁, hr₁, hres⟩) hred y hy
    · rintro ⟨g', ⟨r₁', hr₁', hres'⟩, hred'⟩
      have hγ' : ∀ y, r⁻¹ (Loc.inX X.E (R.N j) (cOf R j) y) = Loc.inX X.E (R.N j) (cOf R j) (γ⁻¹ y) := by
        intro y
        show r.symm _ = _
        rw [LinearEquiv.symm_apply_eq, hγ]
        show _ = Loc.inX X.E (R.N j) (cOf R j) (γ (γ.symm y))
        rw [LinearEquiv.apply_symm_apply]
      have hmem : r * r₁' * r⁻¹ ∈ Loc.Cbe (Jat (Pr := Pr) true j w.1) (r * h' * κ) := by
        refine (cbe_iff _ hr hκ).2 ?_
        rwa [show r⁻¹ * (r * r₁' * r⁻¹) * r = r₁' by group]
      refine ⟨γ * g' * γ⁻¹, ⟨r * r₁' * r⁻¹, hmem, fun y => GlobalTheory.Proof.level_eq_parahoric_category.conj_res hγ' hres' y⟩, ?_⟩
      intro y hy
      have e : ∀ (Q A : GL (Fin (R.N j)) (𝓞 X.E ⧸ w.1.asIdeal)), Q * (Q⁻¹ * A * Q⁻¹⁻¹) * Q⁻¹ = A := by
        intro Q A
        group
      have := red_conj γg (hint' ⟨r₁', hr₁', hres'⟩) hred' y hy
      rw [map_inv, e] at this
      exact this
  · intro hbar hbar' hx
    obtain ⟨g, ⟨r₁, hr₁, hres⟩, hred⟩ := (hG hbar.1).1 hbar.2
    have hgint := hint ⟨r₁, hr₁, hres⟩
    have hr₁' := (cbe_iff _ hr hκ).1 hr₁
    have hres' := GlobalTheory.Proof.level_eq_parahoric_category.conj_res hγ hres
    have hred' : ∀ y ∈ stdAt X.E (R.N j) w.1, redV w.1 ((γ⁻¹ * g * γ) y) = hbar'.1.1.mulVec (redV w.1 y) := by
      intro y hy
      rw [hx]
      exact red_conj γg⁻¹ hgint hred y hy
    have e1 := hC hbar g r₁ hr₁ hres hred
    have e2 := hC' hbar' (γ⁻¹ * g * γ) (r⁻¹ * r₁ * r) hr₁' hres' hred'
    refine Units.ext ?_
    rw [e1, e2, GlobalTheory.Proof.level_eq_parahoric_category.n1Arg_conj_eq hr hr₁.1]

    have hr₁s : r₁ ∈ stabL X.E _ (LocE.lamY w.1 (qOf w.1) (R.N j) (cOf R j) fun i => i + 1) := by
      have h1 : (r * h' * κ)⁻¹ * r₁ * (r * h' * κ)⁻¹⁻¹ ∈ Jat (Pr := Pr) true j w.1 := hr₁.2
      have h2 := jat_le_stab_lamY true j w.1 hP _ h1
      have h3 := mul_mem (mul_mem hst h2) (inv_mem hst)
      rw [show r * h' * κ * ((r * h' * κ)⁻¹ * r₁ * (r * h' * κ)⁻¹⁻¹) * (r * h' * κ)⁻¹ = r₁ by group] at h3
      unfold lamYat at h3
      rw [if_pos hP] at h3
      exact h3
    have hq := GlobalTheory.TopStep.qOf_ne_zero (P := w.1) (E := X.E)
    have hia := GlobalTheory.Mem.LevFin.intAt_n1Arg_G hq r₁ hr₁s
    have ea : ((qOf w.1 : ℕ) : X.E) * Loc.n1Arg r₁ / ((qOf w.1 : ℕ) : X.E) = Loc.n1Arg r₁ := by
      field_simp
    have p1 := hpsi _ hia
    have p2 := hpsi' _ hia
    rw [ea] at p1 p2
    rw [p1, p2]
    congr 1

    rw [lamRow_tup Ch mu mu' j hP]
    have ht : h'⁻¹ * (r⁻¹ * r₁ * r) * h'⁻¹⁻¹ ∈ Jat (Pr := Pr) true j w.1 := hr₁'.2
    rw [inv_inv] at ht
    have e : (r * h' * κ)⁻¹ * r₁ * (r * h' * κ) = κ⁻¹ * (h'⁻¹ * (r⁻¹ * r₁ * r) * h') * κ := by group
    rw [e]
    generalize h'⁻¹ * (r⁻¹ * r₁ * r) * h' = t at ht ⊢
    have LM := GlobalTheory.SymLevelMul.lamRow_mul Ch mu' j w.1 hjm hP
    have hκi : κ⁻¹ ∈ Jat (Pr := Pr) (R := R) true j w.1 := inv_mem hκ
    rw [LM _ (mul_mem hκi ht) _ hκ, LM _ hκi _ ht]
    have e3 : lamRow Ch mu' true j w.1 t.toLinearMap =
        lamRow Ch mu' true j w.1 t.toLinearMap * lamRow Ch mu' true j w.1 (κ⁻¹ : AutY X R j).toLinearMap *
          lamRow Ch mu' true j w.1 κ.toLinearMap := by
      conv_lhs => rw [show t = t * κ⁻¹ * κ by group]
      rw [LM _ (mul_mem ht hκi) _ hκ, LM _ ht _ hκi]
    linear_combination -e3

end GlobalTheory.Mem.Col2.IdxEx.LocMatch
end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Datum Matrix
open scoped InnerProductSpace Classical

namespace GlobalTheory.JointHarm

section Hol

variable {n : ℕ} {P : Type} [AddCommGroup P] [Module ℂ P]

def IsHolRep (ε : Fin n → Bool) (B : P →ₗ⋆[ℂ] P →ₗ[ℂ] ℂ) (π : Matrix (Fin n) (Fin n) ℂ → Module.End ℂ P) : Prop :=
  (∀ x, B x x = 0 → x = 0) ∧ π 1 = 1 ∧
    (∀ a ∈ GlobalTheory.Dec.KC ε, ∀ b ∈ GlobalTheory.Dec.KC ε, π (a * b) = π a * π b) ∧
    (∀ g ∈ GlobalTheory.Dec.KC ε, ∀ x y, B (π g x) y = B x (π gᴴ y)) ∧
    ∀ x y, DifferentiableOn ℂ (fun g : Fin n → Fin n → ℂ => B x (π (Matrix.of g) y))
      {g | Matrix.of g ∈ GlobalTheory.Dec.KC ε}

def IsBottom (ε : Fin n → Bool) (π : Matrix (Fin n) (Fin n) ℂ → Module.End ℂ P) (μ : Fin n → ℝ) (x : P) : Prop :=
  (∀ g ∈ GlobalTheory.Dec.KC ε, IsLoUni g → π g x = x) ∧
    ∀ θ : Fin n → ℝ, π (Matrix.diagonal fun a => Complex.exp ((θ a : ℂ) * Complex.I)) x =
      Complex.exp (((∑ a, μ a * θ a : ℝ) : ℂ) * Complex.I) • x

variable {ι : Type}

def IsHolFam (ε : ι → Fin n → Bool) (B : P →ₗ⋆[ℂ] P →ₗ[ℂ] ℂ)
    (ϖ : (ι → Matrix (Fin n) (Fin n) ℂ) → Module.End ℂ P) : Prop :=
  (∀ x, B x x = 0 → x = 0) ∧ ϖ 1 = 1 ∧
    (∀ a b, (∀ τ, a τ ∈ GlobalTheory.Dec.KC (ε τ)) → (∀ τ, b τ ∈ GlobalTheory.Dec.KC (ε τ)) → ϖ (a * b) = ϖ a * ϖ b) ∧
    ∀ τ, IsHolRep (ε τ) B fun g => ϖ (Pi.mulSingle τ g)

def IsBotFam (ε : ι → Fin n → Bool) (ϖ : (ι → Matrix (Fin n) (Fin n) ℂ) → Module.End ℂ P)
    (μ : ι → Fin n → ℝ) (x : P) : Prop :=
  ∀ τ, IsBottom (ε τ) (fun g => ϖ (Pi.mulSingle τ g)) (μ τ) x

theorem isHolRep_of_isTau {ε : Fin n → Bool} {abelian₂ : Fin n → ℝ} {W : Type} [NormedAddCommGroup W]
    [InnerProductSpace ℂ W] {τ : Matrix (Fin n) (Fin n) ℂ → (W →L[ℂ] W)} {w : W} (h : GlobalTheory.Dec.IsTau ε abelian₂ τ w) :
    IsHolRep ε (innerₛₗ ℂ) (fun g => (τ g : W →ₗ[ℂ] W)) ∧
      IsBottom ε (fun g => (τ g : W →ₗ[ℂ] W)) (-abelian₂) w := by
  obtain ⟨-, ⟨h1, hm⟩, hd, ha, -, -, hw, hl⟩ := h
  refine ⟨⟨fun x hx => inner_self_eq_zero.1 hx, ?_, fun a ha b hb => ?_, ha, hd⟩, hl, fun θ => hw θ ⟨?_, ?_⟩⟩
  · show (τ 1 : W →ₗ[ℂ] W) = 1
    rw [h1]; rfl
  · show (τ (a * b) : W →ₗ[ℂ] W) = _
    rw [hm a ha b hb]; rfl
  · rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose,
      Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext a
    simp [← Complex.exp_conj, ← Complex.exp_add]
  · simp [Formalism.REAL.Jm, Matrix.diagonal_mul_diagonal, mul_comm]

end Hol

section Fock

variable {D : D7} {m n : ℕ}

def fsub (ε : D.what₂.Tau → Fin m → Bool) (k : D.what₂.Tau → Matrix (Fin m) (Fin m) ℂ)
    (u : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ) : PolF D m n →ₐ[ℂ] PolF D m n :=
  MvPolynomial.aeval fun v => ∑ a : Fin m, ∑ b : Fin n,
    MvPolynomial.C (if ε v.1 v.2.1 = true then k v.1 a v.2.1 * (u v.1)⁻¹ v.2.2 b
      else (k v.1)⁻¹ v.2.1 a * u v.1 b v.2.2) * MvPolynomial.X (v.1, a, b)

def detP (ε : Fin m → Bool) (k : Matrix (Fin m) (Fin m) ℂ) : ℂ :=
  ((1 / 2 : ℂ) • (1 + Formalism.REAL.Jm ε) * k + (1 / 2 : ℂ) • (1 - Formalism.REAL.Jm ε)).det

def detM (ε : Fin m → Bool) (k : Matrix (Fin m) (Fin m) ℂ) : ℂ :=
  ((1 / 2 : ℂ) • (1 - Formalism.REAL.Jm ε) * k + (1 / 2 : ℂ) • (1 + Formalism.REAL.Jm ε)).det

def fchar (ε : D.what₂.Tau → Fin m → Bool) (x₁ x₂ x₃ : D.what₂.Tau → ℤ)
    (k : D.what₂.Tau → Matrix (Fin m) (Fin m) ℂ) (u : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ) : ℂ :=
  ∏ τ, detP (ε τ) (k τ) ^ x₁ τ * detM (ε τ) (k τ) ^ x₂ τ * (u τ).det ^ x₃ τ

def fact (ε : D.what₂.Tau → Fin m → Bool) (x₁ x₂ x₃ : D.what₂.Tau → ℤ)
    (k : D.what₂.Tau → Matrix (Fin m) (Fin m) ℂ) (u : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ) :
    Module.End ℂ (PolF D m n) :=
  fchar ε x₁ x₂ x₃ k u • (fsub ε k u).toLinearMap

def factK (n : ℕ) (ε : D.what₂.Tau → Fin m → Bool) (x₁ x₂ x₃ : D.what₂.Tau → ℤ)
    (g : D.what₂.Tau → Matrix (Fin m) (Fin m) ℂ) : Module.End ℂ (PolF D m n) :=
  fact ε x₁ x₂ x₃ (fun τ => ((g τ)⁻¹)ᵀ) 1

def factU (ε : D.what₂.Tau → Fin m → Bool) (x₁ x₂ x₃ : D.what₂.Tau → ℤ)
    (u : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ) : Module.End ℂ (PolF D m n) :=
  fact ε x₁ x₂ x₃ 1 u

def wtK (p : ℕ) (ap am : ℕ → ℕ) (x₁ x₂ : ℤ) (a : Fin m) : ℤ :=
  if (a : ℕ) < p then (ap a : ℤ) + x₁ else -(am (m - 1 - a) : ℤ) + x₂

def wtU (p q : ℕ) (ap am : ℕ → ℕ) (x₃ : ℤ) (j : Fin n) : ℤ :=
  -(if (j : ℕ) < p then (ap j : ℤ) else 0) + (if n - 1 - j < q then (am (n - 1 - j) : ℤ) else 0) + x₃

end Fock

def vact {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n) (u : ι → Matrix (Fin n) (Fin n) ℂ) :
    Module.End ℂ (Pol ℂ ι n) :=
  (∏ τ, (u τ).det ^ (-(lam τ).detShift)) • (Formalism.GradedWeylDivisibility.blockAct ℂ fun τ => (u τ)⁻¹).toLinearMap

end GlobalTheory.JointHarm

end
end

section

set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist

namespace GlobalTheory

theorem twistConeVanishing_of_cut : ∀ {Y : Scheme.{0}} (A N : LB Y), A.IsLB → N.IsLB → ∀ (r : ℕ), 1 ≤ r → ∀ (hM : (lbPow (tens (lbPow N 2) A) r).IsLB) (s : (lbPow (tens (lbPow N 2) A) r).Sec) (G : Y.Modules), (∃ j₁ : ℕ, ∀ j m : ℕ, j₁ ≤ j → m < 2 * r → ∀ p, 0 < p → Subsingleton (coh (twist G (tens (lbPow A j) (lbPow N m))) p)) → TwistConeVanishing A N (kernel (cutHom G hM s)) → TwistConeVanishing A N (cokernel (cutHom G hM s)) → TwistConeVanishing A N G := by
  intro Y A N hA hN r hr hM s G ⟨j₁, h₁⟩ ⟨jK, hK⟩ ⟨jC, hC⟩
  set φ := cutHom G hM s
  let ψ := Abelian.factorThruImage φ
  have hψ : ψ ≫ kernel.ι (cokernel.π φ) = φ := Abelian.image.fac φ
  have : Epi ψ := inferInstanceAs (Epi (Abelian.factorThruImage φ))
  have hS₂ : (ShortComplex.mk (kernel.ι (cokernel.π φ)) (cokernel.π φ)
      (kernel.condition _)).ShortExact := { exact := ShortComplex.exact_kernel _ }
  have hS₁ : (ShortComplex.mk (kernel.ι ψ) ψ (kernel.condition _)).ShortExact :=
    { exact := ShortComplex.exact_kernel _ }
  let eK : kernel ψ ≅ kernel φ := (kernelCompMono ψ _).symm ≪≫ kernelIsoOfEq hψ
  have arith : ∀ (a n : Pic Y) (j m : ℕ), r ≤ j → 2 * r ≤ m →
      (j - r) • a + (m - 2 * r) • n = (-1 : ℤ) • (r • (2 • n + a)) + (j • a + m • n) := by
    intro a n j m h₁ h₂
    obtain ⟨j', rfl⟩ := Nat.exists_eq_add_of_le h₁
    obtain ⟨m', rfl⟩ := Nat.exists_eq_add_of_le h₂
    simp only [Nat.add_sub_cancel_left]
    module
  set J := max j₁ (max jK jC) with hJ
  have hJ₁ : j₁ ≤ J := le_max_left _ _
  have hJK : jK ≤ J := (le_max_left _ _).trans (le_max_right _ _)
  have hJC : jC ≤ J := (le_max_right _ _).trans (le_max_right _ _)
  have key : ∀ m j, m ≤ j → 2 * J + m ≤ 2 * j → ∀ p, 0 < p →
      Subsingleton (coh (twist G (tens (lbPow A j) (lbPow N m))) p) := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro j hmj hJj p hp
      by_cases hm : m < 2 * r
      · exact h₁ j m (by omega) hm p hp
      · push_neg at hm
        have hT : (tens (lbPow A j) (lbPow N m)).IsLB := isLB_tens (isLB_lbPow hA j) (isLB_lbPow hN m)
        have e₁ := Twist.shortExact_map hT hS₁
        have e₂ := Twist.shortExact_map hT hS₂
        obtain ⟨iso⟩ : Nonempty (twist (twist G (lbZPow (lbPow (tens (lbPow N 2) A) r) (-1))) (tens (lbPow A j) (lbPow N m)) ≅
            twist G (tens (lbPow A (j - r)) (lbPow N (m - 2 * r)))) := by
          refine nonempty_twist_twist_iso_of_cls_eq G (isLB_lbZPow hM (-1)) hT
            (isLB_tens (isLB_lbPow hA _) (isLB_lbPow hN _)) ?_
          rw [cls_tens (isLB_lbPow hA _) (isLB_lbPow hN _), cls_tens (isLB_lbPow hA _) (isLB_lbPow hN _),
            cls_lbZPow hM, cls_lbPow_tens_lbPow hN hA, cls_lbPow hA, cls_lbPow hN, cls_lbPow hA, cls_lbPow hN]
          exact arith _ _ j m (by omega) hm
        have hmid : Subsingleton (cohOn (twist (twistZ G (lbPow (tens (lbPow N 2) A) r) (-1))
            (tens (lbPow A j) (lbPow N m))) ⊤ p) := by
          have := ih (m - 2 * r) (by omega) (j - r) (by omega) (by omega) p hp
          exact (cohOn.mapIso ℤ ⊤ p iso).toEquiv.subsingleton
        have hker : Subsingleton (cohOn (twist (kernel ψ) (tens (lbPow A j) (lbPow N m))) ⊤ (p + 1)) := by
          have := hK j m (by omega) hmj (p + 1) (by omega)
          exact @Equiv.subsingleton _ _ (cohOn.mapIso ℤ ⊤ (p + 1) ((twistFunctor _).mapIso eK)).toEquiv this
        have himg := cohOn.subsingleton₃ e₁ ⊤ p hmid hker
        exact cohOn.subsingleton₂ e₂ ⊤ p himg (hC j m (by omega) hmj p hp)
  exact ⟨2 * J, fun j m hj hmj p hp => key m j hmj (by omega) p hp⟩

end GlobalTheory
end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.Col Formalism.L2.DIV GlobalTheory.QNormal GlobalTheory.Mem.Col2.IdxEx

theorem _root_.GlobalTheory.T.latticeNormalForm_via_matrix : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (j : ℕ) (P : HeightOneSpectrum (𝓞 X.E)), P ∉ Pr.vGs → ∀ h : AutY X R j, GlobalTheory.IndefiniteRowSideFullHecke.SandwichNormalForm.NF Pr j P h → ∃ (e : Fin (cOf R j) → ℤ) (z : Fin (R.N j) → X.E), (∀ i, -(j : ℤ) ≤ e i ∧ e i ≤ 0) ∧ (fun l : Fin (R.N j + cOf R j) => if hl : l.1 < R.N j then z ⟨l.1, hl⟩ else 0) ∈ lamYat (Pr := Pr) (R := R) j P ∧ (lamYat (Pr := Pr) (R := R) j P).map (h.toLinearMap.restrictScalars (𝓞 X.E)) = (lamYat (Pr := Pr) (R := R) j P).map ((Matrix.toLin' (_root_.GlobalTheory.Mem.Col2.IdxEx.nfMat (R.N j) (cOf R j) (qOf P : X.E) e z)).restrictScalars (𝓞 X.E)) := by
  first | exact @GlobalTheory.Mem.Col2.IdxEx.nf_matrix | exact GlobalTheory.Mem.Col2.IdxEx.nf_matrix | (intros; apply GlobalTheory.Mem.Col2.IdxEx.nf_matrix <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.Col Formalism.L2.DIV GlobalTheory.QNormal GlobalTheory.Mem.Col2.IdxEx

theorem _root_.GlobalTheory.T.admissibleRepresentatives_finite_level_cosets : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (sharp : Bool) (j : ℕ) (P : HeightOneSpectrum (𝓞 X.E)), ∃ (ι : Type) (_ : Finite ι) (f : AutY X R j → ι), ∀ h h' : AutY X R j, admitted Pr j P h → admitted Pr j P h' → f h = f h' → h⁻¹ * h' ∈ Jat (Pr := Pr) sharp j P := by
  first | exact @GlobalTheory.Mem.Col2.IdxFin.exists_finite_index_of_adm_cosets | exact GlobalTheory.Mem.Col2.IdxFin.exists_finite_index_of_adm_cosets | (intros; apply GlobalTheory.Mem.Col2.IdxFin.exists_finite_index_of_adm_cosets <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.Col Formalism.L2.DIV GlobalTheory.QNormal GlobalTheory.Mem.Col2.IdxEx

theorem _root_.GlobalTheory.T.levelCharacter_stepZero_typePrime : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (P : rowSG Pr sel mu) (hP : P.1 ∈ Pr.vGs), cst.sharp = true → (∀ a : X.E, IntAt P.1 a → cst.psi P (a / (qOf P.1 : X.E)) = psi0P Ch P.1 (redP P.1 a)) → ChrG Ch sel mu cst 0 P 1 (colLev Ch 0 ⟨P.1, hP⟩) := by
  first | exact @GlobalTheory.Proof.levelCharacter_stepZero_typePrime.chrG_zero | exact GlobalTheory.Proof.levelCharacter_stepZero_typePrime.chrG_zero | (intros; apply GlobalTheory.Proof.levelCharacter_stepZero_typePrime.chrG_zero <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.Col Formalism.L2.DIV GlobalTheory.QNormal GlobalTheory.Mem.Col2.IdxEx

theorem _root_.GlobalTheory.T.level_stepZero_at_twistPrime_full : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (P : rowSG Pr sel mu), P.1 ∉ Pr.vGs → cst.Ok → GrpQ (R := R) sel mu cst 0 P 1 ⟨⊤, 1⟩ ∧ ChrQ Ch sel mu cst 0 P 1 ⟨⊤, 1⟩ := by
  first | exact @GlobalTheory.Mem.Col2.IdxExZeroQ.zero_level | exact GlobalTheory.Mem.Col2.IdxExZeroQ.zero_level | (intros; apply GlobalTheory.Mem.Col2.IdxExZeroQ.zero_level <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.Col Formalism.L2.DIV GlobalTheory.QNormal GlobalTheory.Mem.Col2.IdxEx

theorem _root_.GlobalTheory.T.exists_levelGroup_mod_typePrime : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (j : ℕ) (P : rowSG Pr sel mu) (h : AutY X R j), cst.Ok → P.1 ∈ Pr.vGs → GlobalTheory.IndefiniteRowSideFullHecke.SourceLatticeInvariance.DegOneUnram P.1 → h ∈ stabL X.E _ (lamYat (Pr := Pr) (R := R) j P.1) → prCat (Pr := Pr) cst.sharp j P.1 h ≤ GLint X.E (R.N j) P.1 → (∀ y : HomE X.E (R.N j + cOf R j) (R.N j + cOf R j), (∀ x ∈ lamYat (Pr := Pr) (R := R) j P.1, y x ∈ lamYat (Pr := Pr) (R := R) j P.1) → lamRow Ch mu cst.sharp j P.1 (LinearMap.id + (qOf P.1 : X.E) • y) = 1) → ChiMul Ch sel mu cst j P h → ChiTriv Ch sel mu cst j P h → ∃ lev : Lev (𝓞 X.E ⧸ P.1.asIdeal) X.K (R.N j), GrpG sel mu cst j P h lev ∧ ChrG Ch sel mu cst j P h lev := by
  first | exact @GlobalTheory.Mem.Col2.LevMod.exists_levG | exact GlobalTheory.Mem.Col2.LevMod.exists_levG | (intros; apply GlobalTheory.Mem.Col2.LevMod.exists_levG <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.Col Formalism.L2.DIV GlobalTheory.QNormal GlobalTheory.Mem.Col2.IdxEx

theorem _root_.GlobalTheory.T.levelGroupReduction_stepZero_typePrime : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (P : rowSG Pr sel mu) (hP : P.1 ∈ Pr.vGs), cst.sharp = true → GlobalTheory.IndefiniteRowSideFullHecke.SourceLatticeInvariance.DegOneUnram P.1 → GrpG sel mu cst 0 P 1 (colLev Ch 0 ⟨P.1, hP⟩) := by
  first | exact @GlobalTheory.Mem.ZeroGrp.grpG_zero | exact GlobalTheory.Mem.ZeroGrp.grpG_zero | (intros; apply GlobalTheory.Mem.ZeroGrp.grpG_zero <;> assumption)
end

section

open Formalism.BasicNotions Formalism.L2.Forms Formalism.UG Formalism.L2.GlobalTheoryTheory.LocalLatticeBases NumberField IsDedekindDomain Matrix GlobalTheory.LevelHecke
open scoped TensorProduct

theorem _root_.GlobalTheory.T.levelPrime_unramifiedUniformizer : ∀ (D : D7) (u : D.what₂.Word) (A : AtTTied u) (v : (D.mem u).A.vT), Unram (A.res v) (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) := by
  first | exact @GlobalTheory.LevelUnram.unram | exact GlobalTheory.LevelUnram.unram | (intros; apply GlobalTheory.LevelUnram.unram <;> assumption)
end

section


theorem _root_.GlobalTheory.T.exists_harishChandraType_dualWeylModuleFockNorm : ∀ (n : ℕ) (lam : Formalism.BasicNotions.DomWeight n), ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H) (π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (e : H →ₗ[ℂ] MvPolynomial (Fin n × Fin n) ℂ), Formalism.MainNotions.S.IsHCTypeU n (fun i => (lam.w i : ℝ) + ((Formalism.BasicNotions.rhoVec n i : ℚ) : ℝ)) π ∧ Function.Injective e ∧ (∀ x, e x ∈ Formalism.BasicNotions.nablaSq ℂ n lam) ∧ ∀ g : GL (Fin n) ℂ, (g : Matrix (Fin n) (Fin n) ℂ) ∈ Matrix.unitaryGroup (Fin n) ℂ → ∀ x, e (π (g : Matrix (Fin n) (Fin n) ℂ) x) = Formalism.BasicNotions.sqAct ℂ n lam g (e x) := by
  first | exact @GlobalTheory.NablaType.exists_isHCTypeU_nablaSq | exact GlobalTheory.NablaType.exists_isHCTypeU_nablaSq | (intros; apply GlobalTheory.NablaType.exists_isHCTypeU_nablaSq <;> assumption)
end
