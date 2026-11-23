module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle463
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle290
import Formalism.LocalToGlobal.Columns.BaseLemmas
public import Formalism.LocalToGlobal.Columns.RecLevelLocP
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle097
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemZmuOfPowPred
public import Formalism.LocalToGlobal.Columns.ChainLawTw
import Formalism.LocalToGlobal.Columns.RecLevelDiv
import Formalism.LocalToGlobal.Columns.RecLevelSym
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemSmulLk
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle015
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle392
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle381
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle465
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle447
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle004
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoeffZeroNeOfMonicIrr
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle468
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
import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle003
import Formalism.AlgebraicWeights.IsAlgWeight
import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.Bundle001
import ReciprocityTheory.Automorphisms.PlaceA

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.AdT

theorem exists_SBof_over : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (a : I.ι) (v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F)), v ∈ badG (I.rec7 l Z) ∨ I.UnderQ a v → ∃ P ∈ SBof I a, Formalism.L2.Col.IsOver v (GlobalTheory.TwU.seamP (sm I l Z) P) := by
  classical
  intro B X I hOk l Z a v hv
  obtain ⟨-, hPr, -⟩ := base_fields_primes_ok B X
  rcases hv with hv | ⟨P, hP, rfl⟩
  · have key : ∀ (i : Fin 2), v ∈ plUnder (I.rec7 l Z).host.F (E := (I.rec7 l Z).host.E) ((B.primes X).vG i) ↔ ((B.primes X).g i : 𝓞 (I.rec7 l Z).host.F) ∈ v.asIdeal := by
      intro i
      have h0 : B.fields.conjO ((B.primes X).piG i) ≠ 0 := by
        intro h
        have h1 := hPr.piG_norm i
        rw [h, mul_zero] at h1
        exact (Nat.cast_ne_zero.2 (hPr.g_prime i).ne_zero) h1.symm
      refine mem_plUnder_iff_norm (I.rec7 l Z).sp.cm (fun P => mem_divs h0 P) ((B.primes X).g i) ?_ v
      have h2 : cO (I.rec7 l Z).host.E (B.fields.conjO ((B.primes X).piG i)) = (B.primes X).piG i := cO_cO ((B.primes X).piG i)
      rw [h2]
      have h3 : B.fields.conjO ((B.primes X).piG i) * (B.primes X).piG i = ((B.primes X).g i : 𝓞 B.fields.E) := by
        rw [mul_comm]
        exact hPr.piG_norm i
      exact h3
    have hv' : v ∈ plUnder (I.rec7 l Z).host.F (E := (I.rec7 l Z).host.E) (B.primes X).vGs := by
      rcases hv with h | h
      · obtain ⟨P, hP, hPv⟩ := (key 0).2 h
        exact ⟨P, Finset.mem_union_left _ hP, hPv⟩
      · obtain ⟨P, hP, hPv⟩ := (key 1).2 h
        exact ⟨P, Finset.mem_union_right _ hP, hPv⟩
    obtain ⟨P, hP, hPv⟩ := hv'
    refine ⟨P, Finset.mem_union_left _ hP, ?_⟩
    exact hPv
  · refine ⟨P, Finset.mem_union_right _ hP, ?_⟩
    exact rfl

end GlobalTheory.Mem.Col2.AdT
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.AdT.CosShape

section Gen

variable {E : Type} [Field E] [NumberField E] {n : ℕ}

theorem pow_smul_mem (S : Submodule (𝓞 E) (Sp E n)) (r : 𝓞 E) (k : ℕ) {x : Sp E n} (hx : x ∈ S) :
    ((r : E) ^ k) • x ∈ S := by

  have h : ((r : E) ^ k) • x = (r ^ k) • x := by
    rw [← algebraMap_smul E (r ^ k) x]
    simp
  rw [h]
  exact S.smul_mem _ hx

theorem core (S₀ L : Submodule (𝓞 E) (Sp E n)) (F : Sp E n ≃ₗ[E] Sp E n) (hF : ∀ w ∈ L, F.symm w ∈ S₀)
    (c : E) (hc : c ≠ 0) (hpow : ∀ (S : Submodule (𝓞 E) (Sp E n)) (k : ℕ) (x : Sp E n), x ∈ S → c ^ k • x ∈ S)
    (Y : Set (Sp E n)) (y₀ : Sp E n) (e e' : ℕ) (hY0 : y₀ ∈ Y) (hY : ∀ y ∈ Y, (c ^ e)⁻¹ • (y - y₀) ∈ L)
    (hy₀ : c ^ e' • y₀ ∈ L) (C : Set (Sp E n)) (hC : ∀ z, z ∈ C ↔ ∃ y ∈ Y, (c ^ e)⁻¹ • (z - F.symm y) ∈ S₀) :
    C.Nonempty ∧ (∀ y ∈ Y, F.symm y ∈ C) ∧ ∀ z ∈ C, (∀ z', z' ∈ C ↔ (c ^ e)⁻¹ • (z' - z) ∈ S₀) ∧
      ∀ (g g' : Sp E n ≃ₗ[E] Sp E n) (D : ℕ), (∀ x, g' x ∈ S₀ ↔ x ∈ S₀) →
        (∀ x ∈ S₀, (c ^ D)⁻¹ • (g x - g' x) ∈ S₀) → e + e' ≤ D →
        (c ^ e)⁻¹ • (g z - z) ∈ S₀ → ∀ z', g' z' ∈ C ↔ z' ∈ C := by

  have hYY : ∀ y ∈ Y, ∀ y' ∈ Y, (c ^ e)⁻¹ • (F.symm y - F.symm y') ∈ S₀ := by
    intro y hy y' hy'
    have h1 := hF _ (hY y hy)
    have h2 := hF _ (hY y' hy')
    have h3 : (c ^ e)⁻¹ • (F.symm y - F.symm y') =
        F.symm ((c ^ e)⁻¹ • (y - y₀)) - F.symm ((c ^ e)⁻¹ • (y' - y₀)) := by
      simp only [LinearEquiv.map_smul, map_sub]
      rw [← smul_sub]
      congr 1
      abel
    rw [h3]
    exact S₀.sub_mem h1 h2
  have hself : ∀ y ∈ Y, F.symm y ∈ C := by
    intro y hy
    exact (hC _).2 ⟨y, hy, by simp⟩

  have hmem : ∀ z ∈ C, ∀ z', z' ∈ C ↔ (c ^ e)⁻¹ • (z' - z) ∈ S₀ := by
    intro z hz z'
    obtain ⟨y₁, hy₁, hz1⟩ := (hC z).1 hz
    constructor
    · intro hz'
      obtain ⟨y₂, hy₂, hz2⟩ := (hC z').1 hz'
      have key := S₀.add_mem (S₀.sub_mem hz2 hz1) (hYY y₂ hy₂ y₁ hy₁)
      convert key using 1
      rw [← smul_sub, ← smul_add]
      congr 1
      abel
    · intro h
      refine (hC z').2 ⟨y₁, hy₁, ?_⟩
      have key := S₀.add_mem h hz1
      convert key using 1
      rw [← smul_add]
      congr 1
      abel
  refine ⟨⟨F.symm y₀, hself y₀ hY0⟩, hself, fun z hz => ⟨hmem z hz, ?_⟩⟩
  intro g g' D hg' hD hle hgz z'
  obtain ⟨y₁, hy₁, hz1⟩ := (hC z).1 hz
  have hce : c ^ e ≠ 0 := pow_ne_zero _ hc

  have hx₀ : c ^ e' • z ∈ S₀ := by
    have a1 : c ^ e' • (c ^ e • ((c ^ e)⁻¹ • (z - F.symm y₁))) ∈ S₀ := hpow _ _ _ (hpow _ _ _ hz1)
    have a2 : c ^ e' • (c ^ e • ((c ^ e)⁻¹ • (F.symm y₁ - F.symm y₀))) ∈ S₀ :=
      hpow _ _ _ (hpow _ _ _ (hYY y₁ hy₁ y₀ hY0))
    have a3 : F.symm (c ^ e' • y₀) ∈ S₀ := hF _ hy₀
    rw [smul_inv_smul₀ hce] at a1 a2
    rw [LinearEquiv.map_smul] at a3
    have a4 := S₀.add_mem (S₀.add_mem a1 a2) a3
    convert a4 using 1
    rw [← smul_add, ← smul_add]
    congr 1
    abel

  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hle
  have hdiff : (c ^ e)⁻¹ • (g z - g' z) ∈ S₀ := by
    have b1 := hpow S₀ k _ (hD _ hx₀)
    convert b1 using 1
    rw [LinearEquiv.map_smul, LinearEquiv.map_smul, ← smul_sub, smul_smul, smul_smul]
    congr 1
    rw [pow_add, pow_add]
    field_simp
  have ht : (c ^ e)⁻¹ • (g' z - z) ∈ S₀ := by
    have b2 := S₀.sub_mem hgz hdiff
    convert b2 using 1
    rw [← smul_sub]
    congr 1
    abel
  rw [hmem z hz (g' z'), hmem z hz z']
  have hsplit : (c ^ e)⁻¹ • (g' z' - z) = g' ((c ^ e)⁻¹ • (z' - z)) + (c ^ e)⁻¹ • (g' z - z) := by
    rw [LinearEquiv.map_smul, ← smul_add, map_sub]
    congr 1
    abel
  rw [hsplit, add_mem_cancel_right ht]
  exact hg' _

end Gen

end GlobalTheory.Mem.Col2.AdT.CosShape

namespace GlobalTheory.Mem.Col2.AdT.CosShape



open Classical in
theorem cosShape : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (u : B.Word) (a : I.ι) (i : ℕ) (p : PtAt B.R I.sel (I.tup a) (I.cst a) u i) (P : SBof I a), (i + 1 ≠ B.R.m → cosetIn p P = ∅) ∧ (i + 1 = B.R.m → (cosetIn p P).Nonempty ∧ (∀ y ∈ p.1.2, (frsF I.sel (I.tup a) p.1.1 P).symm y ∈ cosetIn p P) ∧ ∀ z ∈ cosetIn p P, (∀ z', z' ∈ cosetIn p P ↔ GlobalTheory.TwU.SameCoset I.sel (I.tup a) (I.cst a) P z' z) ∧ ∀ g g' : Sp B.fields.E (B.R.N i) ≃ₗ[B.fields.E] Sp B.fields.E (B.R.N i), g' ∈ Formalism.L2.Col.GLint B.fields.E (B.R.N i) P.1 → CongE P.1 ((I.cst a).D P) g g' → GlobalTheory.TwU.SameCoset I.sel (I.tup a) (I.cst a) P (g z) z → ∀ z', g' z' ∈ cosetIn p P ↔ z' ∈ cosetIn p P) := by
  intro B X I hI u a i p P
  refine ⟨fun hi => ?_, fun hi => ?_⟩
  ·
    have h0 : p.1.2 = ∅ := by
      have h := p.2
      rw [ysAt_ys_of_ne (h := hi)] at h
      exact Set.mem_singleton_iff.mp h
    ext z
    simp [cosetIn, h0]
  · have hY := PtAt.mem_ybSet p hi
    unfold ybSet at hY
    obtain ⟨y₀, hy₀, hYeq⟩ := hY

    have hfr : ∀ x, (frsF I.sel (I.tup a) p.1.1 P) x ∈ Formalism.HermitianLatticesTheory.localization₂ P.1.asIdeal p.1.1.deco.1.N ↔
        x ∈ stdAt B.fields.E (B.R.N i) P.1 := by
      intro x
      simp only [frsF]
      split_ifs with h
      · exact (GlobalTheory.TopStep.liftFr_spec p.1.1.deco.2 ⟨P.1, h⟩).1 x
      · exact p.1.1.2 ⟨P.1, (Finset.mem_union.mp P.2).resolve_left h⟩ x
    have hF : ∀ w ∈ Formalism.HermitianLatticesTheory.localization₂ P.1.asIdeal p.1.1.deco.1.N,
        (frsF I.sel (I.tup a) p.1.1 P).symm w ∈ stdAt B.fields.E (B.R.N i) P.1 := by
      intro w hw
      rw [← hfr, LinearEquiv.apply_symm_apply]
      exact hw
    have hc : ((qOf P.1 : ℕ) : B.fields.E) ≠ 0 := by
      exact_mod_cast (GlobalTheory.GO.ChRoot.qOf_pos P.1).ne'
    have hpow : ∀ (S : Submodule (𝓞 B.fields.E) (Sp B.fields.E (B.R.N i))) (k : ℕ) (x : Sp B.fields.E (B.R.N i)),
        x ∈ S → ((qOf P.1 : ℕ) : B.fields.E) ^ k • x ∈ S := by
      intro S k x hx
      have h := pow_smul_mem S ((qOf P.1 : ℕ) : 𝓞 B.fields.E) k hx
      simpa using h
    have hY0 : y₀ ∈ p.1.2 := by
      rw [hYeq, Set.mem_setOf_eq, sub_self]
      exact zero_mem _
    have hY1 := (mem_locLat _ _ _ _).1 hy₀ P
    have hGL : ∀ g' : Sp B.fields.E (B.R.N i) ≃ₗ[B.fields.E] Sp B.fields.E (B.R.N i),
        g' ∈ Formalism.L2.Col.GLint B.fields.E (B.R.N i) P.1 →
          ∀ x, g' x ∈ stdAt B.fields.E (B.R.N i) P.1 ↔ x ∈ stdAt B.fields.E (B.R.N i) P.1 := by
      intro g' hg'
      exact hg'
    by_cases hP : P.1 ∈ (B.primes X).vGs
    ·
      have hYl : ∀ y ∈ p.1.2, (((qOf P.1 : ℕ) : B.fields.E) ^ 0)⁻¹ • (y - y₀) ∈ Formalism.HermitianLatticesTheory.localization₂ P.1.asIdeal p.1.1.deco.1.N := by
        intro y hy
        rw [hYeq, Set.mem_setOf_eq] at hy
        have h := (mem_locLat _ _ _ _).1 hy P
        simpa [hP] using h
      have hy₀' : ((qOf P.1 : ℕ) : B.fields.E) ^ 1 • y₀ ∈ Formalism.HermitianLatticesTheory.localization₂ P.1.asIdeal p.1.1.deco.1.N := by
        simpa [hP] using hY1
      have hC : ∀ z, z ∈ cosetIn p P ↔ ∃ y ∈ p.1.2,
          (((qOf P.1 : ℕ) : B.fields.E) ^ 0)⁻¹ • (z - (frsF I.sel (I.tup a) p.1.1 P).symm y) ∈
            stdAt B.fields.E (B.R.N i) P.1 := by
        intro z
        simp only [cosetIn, Set.mem_setOf_eq, if_pos hP]
      have hSC : ∀ x y : Sp B.fields.E (B.R.N i), GlobalTheory.TwU.SameCoset I.sel (I.tup a) (I.cst a) P x y ↔
          (((qOf P.1 : ℕ) : B.fields.E) ^ 0)⁻¹ • (x - y) ∈ stdAt B.fields.E (B.R.N i) P.1 := by
        intro x y
        rw [GlobalTheory.GO.ChRoot.mem_stdAt']
        simp only [GlobalTheory.TwU.SameCoset, if_pos hP, Pi.smul_apply, smul_eq_mul]
      obtain ⟨k1, k2, k3⟩ := core (stdAt B.fields.E (B.R.N i) P.1) (Formalism.HermitianLatticesTheory.localization₂ P.1.asIdeal p.1.1.deco.1.N)
        (frsF I.sel (I.tup a) p.1.1 P) hF _ hc hpow p.1.2 y₀ 0 1 hY0 hYl hy₀' (cosetIn p P) hC
      refine ⟨k1, k2, fun z hz => ⟨fun z' => ((k3 z hz).1 z').trans (hSC z' z).symm, ?_⟩⟩
      intro g g' hg' hcong hgz z'
      have hD1 := (hI.idx_ok a).depthG P hP
      exact (k3 z hz).2 g g' _ (hGL g' hg') hcong (by omega) ((hSC _ _).1 hgz) z'
    ·
      have hYl : ∀ y ∈ p.1.2, (((qOf P.1 : ℕ) : B.fields.E) ^ (I.cst a).M)⁻¹ • (y - y₀) ∈
          Formalism.HermitianLatticesTheory.localization₂ P.1.asIdeal p.1.1.deco.1.N := by
        intro y hy
        rw [hYeq, Set.mem_setOf_eq] at hy
        have h := (mem_locLat _ _ _ _).1 hy P
        simpa [hP] using h
      have hy₀' : ((qOf P.1 : ℕ) : B.fields.E) ^ (I.cst a).M • y₀ ∈ Formalism.HermitianLatticesTheory.localization₂ P.1.asIdeal p.1.1.deco.1.N := by
        simpa [hP] using hY1
      have hC : ∀ z, z ∈ cosetIn p P ↔ ∃ y ∈ p.1.2,
          (((qOf P.1 : ℕ) : B.fields.E) ^ (I.cst a).M)⁻¹ • (z - (frsF I.sel (I.tup a) p.1.1 P).symm y) ∈
            stdAt B.fields.E (B.R.N i) P.1 := by
        intro z
        simp only [cosetIn, Set.mem_setOf_eq, if_neg hP]
      have hSC : ∀ x y : Sp B.fields.E (B.R.N i), GlobalTheory.TwU.SameCoset I.sel (I.tup a) (I.cst a) P x y ↔
          (((qOf P.1 : ℕ) : B.fields.E) ^ (I.cst a).M)⁻¹ • (x - y) ∈ stdAt B.fields.E (B.R.N i) P.1 := by
        intro x y
        rw [GlobalTheory.GO.ChRoot.mem_stdAt']
        simp only [GlobalTheory.TwU.SameCoset, if_neg hP, Pi.smul_apply, smul_eq_mul]
      obtain ⟨k1, k2, k3⟩ := core (stdAt B.fields.E (B.R.N i) P.1) (Formalism.HermitianLatticesTheory.localization₂ P.1.asIdeal p.1.1.deco.1.N)
        (frsF I.sel (I.tup a) p.1.1 P) hF _ hc hpow p.1.2 y₀ (I.cst a).M (I.cst a).M hY0 hYl hy₀' (cosetIn p P) hC
      refine ⟨k1, k2, fun z hz => ⟨fun z' => ((k3 z hz).1 z').trans (hSC z' z).symm, ?_⟩⟩
      intro g g' hg' hcong hgz z'
      have hD2 := (hI.idx_ok a).depthQ P hP
      exact (k3 z hz).2 g g' _ (hGL g' hg') hcong (by omega) ((hSC _ _).1 hgz) z'

end GlobalTheory.Mem.Col2.AdT.CosShape
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.AdT

open GlobalTheory.TopStep GlobalTheory.LastSteps

theorem lamGBS_top_mul_lam_eq_one : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m) (w : {w // w ∈ Pr.vGs})
    (h0 : GL (Fin (R.N R.m - 1)) (𝓞 X.E ⧸ w.1.asIdeal)) (hh0 : h0 ∈ (rowTyG Ch (rPsymF Ch) w).H)
    (g g' : Sp X.E (R.N R.m) ≃ₗ[X.E] Sp X.E (R.N R.m)) (g'' : Sp X.E ((R.N R.m - 1) + 0) ≃ₗ[X.E] Sp X.E ((R.N R.m - 1) + 0)),
    g'' ∈ LocE.JGsym w.1 (qOf w.1) R.k R.rS R.r R.t (R.N R.m - 1) 0 →
    prXpG X.E (R.N R.m) ∘ₗ g.toLinearMap = g''.toLinearMap ∘ₗ prXpG X.E (R.N R.m) →
    g' ∈ Formalism.L2.Col.GLint X.E (R.N R.m) w.1 →
    (∀ x ∈ stdAt X.E (R.N R.m) w.1, redV w.1 (g' x) =
      ((diagEmb (𝓞 X.E ⧸ w.1.asIdeal) (Nat.sub_le (R.N R.m) 1) h0)⁻¹ : GL (Fin (R.N R.m)) (𝓞 X.E ⧸ w.1.asIdeal)).1.mulVec (redV w.1 x)) →
    CongE w.1 1 g g' →
    LocE.lamGBS (qOf w.1) (psi0P Ch w.1) (chiP Ch w.1) R.k R.r R.t R.m (R.N R.m - 1) 0 g''.toLinearMap *
      (((rowTyG Ch (rPsymF Ch) w).lam ⟨h0, hh0⟩ : X.Kˣ) : X.K) = 1 := by
  intro X Pr R Ch w h0 hh0 g g' g'' hJ hcomm hg' hred hcong
  classical
  obtain ⟨σ₀⟩ : Nonempty (X.K →+* ℂ) := inferInstance
  have hN : R.N R.m = (R.N R.m - 1) + 1 := N_m_succ R
  have ht := t_pos R
  have hrr := r_eq_sym R
  have hX' := rank_X'_eq R
  have hint : g'' ∈ GLint X.E (R.N R.m - 1) w.1 := by
    intro x
    have h1 := (Subgroup.mem_inf.1 hJ).1 x
    rwa [lamY_zero] at h1
  have hredr : ∀ x ∈ stdAt X.E (R.N R.m - 1) w.1, redV w.1 (g'' x) = (h0⁻¹).1.mulVec (redV w.1 x) := by
    intro x hx
    let v : Sp X.E (R.N R.m) := fun l => if hl : l.1 < R.N R.m - 1 then x ⟨l.1, hl⟩ else 0
    have hv : v ∈ stdAt X.E (R.N R.m) w.1 := by
      rw [mem_stdAt]
      intro l
      by_cases hl : l.1 < R.N R.m - 1
      · simp only [v, dif_pos hl]
        exact mem_stdAt.1 hx _
      · simp only [v, dif_neg hl]
        exact intAt_zero
    have hpv : prXpG X.E (R.N R.m) v = x := by
      funext i
      have hi : i.1 < R.N R.m - 1 := i.2
      simp [prXpG, LinearMap.funLeft_apply, v, hi]
    have hgx : g'' x = prXpG X.E (R.N R.m) (g v) := by
      have h2 := LinearMap.congr_fun hcomm v
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe] at h2
      rw [h2, hpv]
    have hc := hcong v hv
    funext i
    have eL : redV w.1 (g'' x) i = redV w.1 (g' v) (Br.iC hN i) := by
      rw [hgx]
      show redP w.1 (g v (Br.iC hN i)) = redP w.1 (g' v (Br.iC hN i))
      have hz := mem_stdAt.1 hc (Br.iC hN i)
      have hq : ((qOf w.1 : ℕ) : X.E) ≠ 0 := qOf_ne_zero
      have e : g v (Br.iC hN i) = g' v (Br.iC hN i) +
          (qOf w.1 : X.E) * (((((qOf w.1 : ℕ) : X.E) ^ 1)⁻¹ • (g v - g' v)) (Br.iC hN i)) := by
        simp only [pow_one, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
        rw [mul_inv_cancel_left₀ hq]
        ring
      rw [e, redP_add_q hz]
    rw [eL, hred v hv, ← map_inv, diagEmb_val, (diagMat_mulVec hN _ _).1 i]
    congr 1
    funext j
    show redP w.1 (v (Br.iC hN j)) = redP w.1 (x j)
    have hj : (Br.iC hN j).1 < R.N R.m - 1 := j.2
    simp only [v, dif_pos hj]
    rfl
  have hM : h0⁻¹ ∈ HJsym (𝓞 X.E ⧸ w.1.asIdeal) (R.N R.m - 1) R.k R.r R.t R.m R.rS (r_le_X' R) := inv_mem hh0
  have e1 : psi0P Ch w.1 = Ch.psi0 w := by
    unfold psi0P
    rw [dif_pos w.2]
  have e2 : chiP Ch w.1 = chiAt Ch w := by
    unfold chiP
    rw [dif_pos w.2]
  have hlam : LocE.lamGBS (qOf w.1) (psi0P Ch w.1) (chiP Ch w.1) R.k R.r R.t R.m (R.N R.m - 1) 0 g''.toLinearMap =
      ((lamJsym (Ch.psi0 w) (chiAt Ch w) (R.N R.m - 1) R.k R.r R.t R.m R.rS (r_le_X' R) ⟨h0⁻¹, hM⟩ : X.Kˣ) : X.K) := by
    rw [e1, e2]
    exact clW_lamGBS_lamJsym σ₀ _ _ hrr ht (by omega) (r_le_X' R) (by omega) ⟨h0⁻¹, hM⟩ g'' hint hredr
  have hr : ((rowTyG Ch (rPsymF Ch) w).lam ⟨h0, hh0⟩ : X.Kˣ) =
      lamJsym (Ch.psi0 w) (chiAt Ch w) (R.N R.m - 1) R.k R.r R.t R.m R.rS (r_le_X' R) ⟨h0, hh0⟩ := rfl
  have hprod : (⟨h0⁻¹, hM⟩ * ⟨h0, hh0⟩ : ↥(HJsym (𝓞 X.E ⧸ w.1.asIdeal) (R.N R.m - 1) R.k R.r R.t R.m R.rS (r_le_X' R))) = 1 :=
    Subtype.ext (inv_mul_cancel h0)
  rw [hlam, hr, ← Units.val_mul, ← map_mul, hprod, map_one, Units.val_one]

end GlobalTheory.Mem.Col2.AdT
end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.HAt Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.HAt



theorem dnCl_of_tie {B : Base} {X : PreX B.toPre} (I : TC B X) (hOk : I.Ok) (hP : TC.Pins B X) (l : I.Laws)
    (Z : TC.Later B (I.cols l)) (H : Formalism.L2.Herm.HermColsCh (I.rec7 l Z))
    (F : ∀ u, FormsTiedSym (I.rec7 l Z) u (H.Ch u) (H.chOf u))
    (hS : ∀ u, I.StdF l Z u (F u) ∧ I.StdLvC l Z u (F u)) (hC : CarH H F) (u) (i : ℕ) (hi : i ≤ (I.rec7 l Z).R.m) (v)
    (c : ((I.rec7 l Z).mem u).C.cls i)
    (g : Module.Dual (((I.rec7 l Z).mem u).A.Fv v) (((I.rec7 l Z).fm u).lk i v c))
    (γ₀ : UJ (sigD (I.rec7 l Z) : (I.rec7 l Z).host.E →+* (I.rec7 l Z).host.E) (gramN (I.rec7 l Z) i hi))
    (hAd : AdC (F u) i hi c (((I.rec7 l Z).fm u).dn i v c g) γ₀.1 ((F u).atT.eV v).1)
    (hloc : Formalism.HermitianLatticesTheory.localization₂ ((F u).atT.Pv v) (Formalism.L2.Forms.mulLat γ₀.1.1
        (Formalism.L2.Forms.Ld (I.rec7 l Z) u i hi (((I.rec7 l Z).fm u).dn i v c g))) =
      Formalism.HermitianLatticesTheory.localization₂ ((F u).atT.Pv v) (clsCrd (I.rec7 l Z) u i hi c))
    (hfv : ∀ (x : Formalism.L2.Forms.Ld (I.rec7 l Z) u i hi (((I.rec7 l Z).fm u).dn i v c g))
      (hx : γ₀.1.1 *ᵥ x.1 ∈ Formalism.L2.Forms.Lk (F u).atT i hi v c),
      ((I.rec7 l Z).fm u).fv i v _ (((F u).lv i hi).pr v _ x) = g (((F u).lv i hi).prk v c ⟨_, hx⟩)) :
    DnCl (F u).atT (F u).lv i v c g (gx i hi γ₀) ∧
      AdOf H u i c (((I.rec7 l Z).fm u).dn i v c g) (gx i hi γ₀) v := by
  refine ⟨⟨?_, ?_, ?_, ?_⟩, GlobalTheory.T.adelic_relation_classes_coordinates I hOk hP l Z H F hS hC u i hi v c _ γ₀ hAd⟩
  · intro q hq hq1 hq2
    haveI := hq.isPrime
    let Q : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.E) :=
      ⟨q, hq.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hq (RingOfIntegers.not_isField _)⟩
    have hu : Q.under (𝓞 (I.rec7 l Z).host.F) ≠ ((F u).atT.eV v).1 := fun h =>
      (GlobalTheory.T.host_primes_over_level_place I hOk hP l Z H F hS hC u v Q h).elim hq1 hq2
    have h1 := GlobalTheory.T.adelic_conjugate_character_standard_forms I hOk hP l Z H F hS hC u i hi v c _ γ₀.1 hAd Q hu
    refine Submodule.map_injective_of_injective
      (f := ((crdN (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) i hi : ((_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).sp.X i).V →ₗ[(_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.E] (Fin ((_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).R.N i) → (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.E)).restrictScalars (𝓞 (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.E)))
      (crdN (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) i hi).injective ?_
    rw [localization_map₂ hi, localization_map₂ hi, lc_gmap]
    exact h1
  · have e : lc ((I.rec7 l Z).sp.X i) (rankN (I.rec7 l Z) i hi) (Formalism.L2.Herm.Ld (I.rec7 l Z) u i (((I.rec7 l Z).fm u).dn i v c g)) =
        Formalism.L2.Forms.Ld (I.rec7 l Z) u i hi (((I.rec7 l Z).fm u).dn i v c g) :=
      dual_co (I.rec7 l Z).sp.cm ((I.rec7 l Z).sp.X i) (rankN (I.rec7 l Z) i hi) ((I.rec7 l Z).clsLat u i _)
    refine Submodule.map_injective_of_injective
      (f := ((crdN (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) i hi : ((_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).sp.X i).V →ₗ[(_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.E] (Fin ((_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).R.N i) → (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.E)).restrictScalars (𝓞 (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.E)))
      (crdN (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) i hi).injective ?_
    rw [localization_map₂ hi, localization_map₂ hi, lc_gmap]
    refine Eq.trans ?_ hloc
    exact congrArg (fun L => Formalism.HermitianLatticesTheory.localization₂ ((F u).atT.Pv v) (Formalism.L2.Forms.mulLat γ₀.1.1 L)) e
  · intro z hz
    rw [prH_eq _ _ hi, prkH_eq _ _ hi]
    have hx : γ₀.1.1 *ᵥ (toLd i hi _ z).1 ∈ Formalism.L2.Forms.Lk (F u).atT i hi v c := by
      rw [show (toLd i hi _ z).1 = crdN (I.rec7 l Z) i hi z.1 from rfl, ← crdN_gx]
      exact (mem_Lk (F u).atT i hi v c _).1 hz
    rw [hfv _ hx]
    exact congrArg g (congrArg _ (Subtype.ext (crdN_gx i hi γ₀ z.1).symm))
  · intro v' hv' z hz
    rw [prH_eq _ _ hi, prH_eq _ _ hi]
    exact GlobalTheory.T.levelFunctional_eq_of_classes_related_at_place I hOk hP l Z H F hS hC u i hi v v' c _ γ₀.1 hAd hv' (toLd i hi c ⟨_, hz⟩) (toLd i hi _ z)
      (crdN_gx i hi γ₀ z.1)

end GlobalTheory.Mem.Col2.HAt



theorem GlobalTheory.Mem.Col2.HAt.dn_move_exists : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (H : Formalism.L2.Herm.HermColsCh (I.rec7 l Z)) (F : ∀ u, FormsTiedSym (I.rec7 l Z) u (H.Ch u) (H.chOf u)), (∀ u, I.StdF l Z u (F u) ∧ I.StdLvC l Z u (F u)) → CarH H F → ∀ u i v (c : ((I.rec7 l Z).mem u).C.cls i) (g : Module.Dual (((I.rec7 l Z).mem u).A.Fv v) (((I.rec7 l Z).fm u).lk i v c)), ∃ γ, i ≤ (I.rec7 l Z).R.m → g ≠ 0 → DnCl (F u).atT (F u).lv i v c g γ ∧ AdOf H u i c (((I.rec7 l Z).fm u).dn i v c g) γ v := by
  intro B X I hOk hP l Z H F hS hC u i v c g
  by_cases hcase : i ≤ (I.rec7 l Z).R.m ∧ g ≠ 0
  · obtain ⟨hi, hg⟩ := hcase
    by_cases hN : i = 0 ∨ i = (I.rec7 l Z).R.m
    · obtain ⟨γ, η, κ, hη, hy, hloc, hfv, -⟩ := (F u).dnN i hi hN v c g hg
      refine ⟨gx i hi γ, fun _ _ => dnCl_of_tie I hOk hP l Z H F hS hC u i hi v c g γ
        ⟨fun _ => ⟨κ.1, κ.2, η.1, η.2, hη, hy⟩, fun h1 h2 => absurd hN (by omega)⟩ hloc hfv⟩
    · have h1 : 1 ≤ i := by omega
      have h2 : i + 1 ≤ (I.rec7 l Z).R.m := by omega
      obtain ⟨hβ, γ, η, κ, hη, hy, hloc, hfv, -⟩ := (F u).dnC i h1 h2 v (H.chOf u i c) ⟨c, rfl⟩ g hg
      refine ⟨gx i hi γ, fun _ _ => dnCl_of_tie I hOk hP l Z H F hS hC u i hi v c g γ
        ⟨fun h => absurd h hN, fun _ _ => ⟨hβ, κ.1, κ.2, η.1, η.2, hη, hy⟩⟩ hloc ?_⟩
      intro x hx
      rw [← (GlobalTheory.T.middleStep_oneLevel_projection_eq_chart_projection I hOk hP l Z H F hS hC u i h1 h2 v (((I.rec7 l Z).fm u).dn i v c g)).1 x x rfl,
        ← (GlobalTheory.T.middleStep_oneLevel_projection_eq_chart_projection I hOk hP l Z H F hS hC u i h1 h2 v c).2 ⟨_, hx⟩ ⟨_, hx⟩ rfl]
      exact hfv x hx
  · exact ⟨1, fun hi hg => absurd ⟨hi, hg⟩ hcase⟩
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

theorem _root_.GlobalTheory.T.cuspParam_of_greenParametrisation : GlobalTheory.Published.GreenCuspidal → ∀ (g : ℕ) [Fact g.Prime] (t : Formalism.CyclotomicNorms.Fbar g →* ℂ) (ht : ∀ x y : Formalism.CyclotomicNorms.Fbar g, x ≠ 0 → y ≠ 0 → t x = t y → x = y) (ζ : ℕ → Formalism.CyclotomicNorms.Fbar g) (hζ : IsGenSys ζ), Formalism.IrreducibleCountingLemmas.TYPES.CuspParam (ZMod g) (convC t ht ζ hζ) := by
  first | exact @GlobalTheory.GreenParam.cuspParam_of_green | exact GlobalTheory.GreenParam.cuspParam_of_green | (intros; apply GlobalTheory.GreenParam.cuspParam_of_green <;> assumption)
end
