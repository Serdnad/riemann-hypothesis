module

public import Formalism.LocalToGlobal.GaloisLevelStructure.Bundle003
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Formalism.LocalToGlobal.HermitianForms.PrkSmul
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GlESymmApply
public import Formalism.HermitianLattices.HermitianLatticesProofs.DualLattice
public import Formalism.LocalToGlobal.GlobalTheory.GL6.PBwLocGen
public import Formalism.LocalToGlobal.GlobalTheory.GL6.Bundle002
import Formalism.LocalToGlobal.GlobalTheory.GL6.PRLocV
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle018
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle025
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle270
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.TwDefs
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormEqZpowOfMemMaxUnramifiedSubfield
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle028
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIntegersCompletion
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle001
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle271
import Development.AbelianVarietyTheory.Definitions.Foundations.CdScaleTieIff
import Formalism.LocalToGlobal.HilbertRowConditions.CenterIdempotentAction
import Formalism.LocalToGlobal.IndefiniteReal.RecTie
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle003
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf

@[expose] public section

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2 Formalism.L2.Host Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.MtIn
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.MtIn.Under

theorem not_both {E : Type} [Field E] [NumberField E] {P : HeightOneSpectrum (𝓞 E)} {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hne : q ≠ p) (h1 : (p : 𝓞 E) ∈ P.asIdeal) (h2 : (q : 𝓞 E) ∈ P.asIdeal) : False := by
  have hc : IsCoprime (q : 𝓞 E) (p : 𝓞 E) := Nat.Coprime.cast ((Nat.coprime_primes hq hp).2 hne)
  obtain ⟨x, y, hxy⟩ := hc
  exact P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2
    (hxy ▸ P.asIdeal.add_mem (P.asIdeal.mul_mem_left _ h2) (P.asIdeal.mul_mem_left _ h1)))

theorem q_mem {D : D7} {P : Pl D.host.E} {q : ℕ} (h : Nat.card (kP P) = q) : (q : 𝓞 D.host.E) ∈ P.asIdeal := by
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast, ← h]
  have := card_nsmul_eq_zero' (G := kP P) (x := 1)
  rwa [nsmul_one] at this

theorem places_under : ∀ (D : D7) (T : Type) (L : LevCh D T) (μ0 : T), L.Is μ0 → (∀ PP, PP ∈ L.Pg ↔ ∃ k v, PP = D.naut.plGw k v) → ∀ (i : Fin D.R.m) (t : T) (PP : Pl D.host.E), PP ∈ L.Pg ∨ PP ∈ L.Q t → ∀ v, NG.OverPl PP v → v ∈ gPl D ∪ qPl D (L.C.mu0 i * L.xiH t) := by
  intro D T L μ0 hL hPg i t PP hPP v hv
  by_cases hg : v ∈ gPl D
  · exact Or.inl hg
  rcases hPP with hP | hQ
  · obtain ⟨k, w, rfl⟩ := (hPg _).1 hP
    exact absurd ⟨_, hv, k, D.naut.plGw_over k w⟩ hg
  · refine Or.inr ⟨hg, PP, hv, fun hu => ?_⟩
    obtain ⟨⟨q, hq1, hq2, -, hq4⟩, -⟩ := hL.Q_pl t PP hQ
    have hm : (L.C.mu0 i).UnrAt PP := (L.C.isMu0 i).unr PP fun l hl =>
      not_both (D.host.g_prime l) hq1 (hq4 l) hl (q_mem hq2)
    have hx : (L.xiH t).UnrAt PP := by
      intro x hx
      have h1 : (L.C.mu0 i).loc PP x * (L.xiH t).loc PP x = 1 := hu x hx
      rwa [hm x hx, one_mul] at h1
    exact (hL.Q_ram t PP).2 (Or.inl hQ) hx

end GlobalTheory.MtIn.Under

end
end

section

open Formalism.BasicNotions Formalism.L2.Forms Formalism.UG Formalism.L2.GlobalTheoryTheory.LocalLatticeBases NumberField IsDedekindDomain Matrix GlobalTheory.LevelHecke
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.LevelHecke.DualConj

variable {E : Type} [Field E] [NumberField E] {n : ℕ}

theorem mem_dualL (σ : E →+* E) (J : Matrix (Fin n) (Fin n) E) (L : Submodule (𝓞 E) (Fin n → E)) (y : Fin n → E) :
    y ∈ dualL σ J L ↔ ∀ x ∈ L, hform σ J x y ∈ (algebraMap (𝓞 E) E).range := by
  have := bwG_span_dualSet σ J L
  change y ∈ ((Submodule.span (𝓞 E) (dualSet σ J L) : Submodule (𝓞 E) (Fin n → E)) : Set (Fin n → E)) ↔ _
  rw [this]; rfl

omit [NumberField E] in
theorem hform_eq (σ : E →+* E) (J : Matrix (Fin n) (Fin n) E) (x y : Fin n → E) :
    hform σ J x y = (fun i => σ (x i)) ⬝ᵥ (J *ᵥ y) := by
  simp only [hform, dotProduct, mulVec, Finset.mul_sum, mul_assoc]

omit [NumberField E] in
theorem hform_unitary (σ : E →+* E) (J : Matrix (Fin n) (Fin n) E) (g : Matrix (Fin n) (Fin n) E)
    (hg : cT σ g * J * g = J) (x y : Fin n → E) : hform σ J (g *ᵥ x) (g *ᵥ y) = hform σ J x y := by
  have e : (fun i => σ ((g *ᵥ x) i)) = (fun i => σ (x i)) ᵥ* cT σ g := by
    funext i
    simp [cT, mulVec, vecMul, dotProduct, mul_comm]
  rw [hform_eq, hform_eq, e, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec, hg]

omit [NumberField E] in
theorem hform_smul_left (σ : E →+* E) (J : Matrix (Fin n) (Fin n) E) (a : E) (x y : Fin n → E) :
    hform σ J (a • x) y = σ a * hform σ J x y := by
  simp only [hform, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum, mul_assoc]

omit [NumberField E] in
theorem hform_smul_right (σ : E →+* E) (J : Matrix (Fin n) (Fin n) E) (a : E) (x y : Fin n → E) :
    hform σ J x (a • y) = a * hform σ J x y := by
  simp only [hform, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

@[reducible] def starOf (σ : E →+* E) (hσ : ∀ x, σ (σ x) = x) : StarRing E where
  star := σ
  star_involutive := hσ
  star_mul a b := by rw [map_mul, mul_comm]
  star_add := map_add σ

theorem dual_lattice_bidual (σ : E →+* E) (hσ : ∀ x, σ (σ x) = x) (J : Matrix (Fin n) (Fin n) E)
    (hJ : IsUnit J.det) (hH : cT σ J = J) (L : Submodule (𝓞 E) (Fin n → E)) (hL : Submodule.IsFullLattice E L) :
    Submodule.IsFullLattice E (dualL σ J L) ∧ dualL σ J (dualL σ J L) = L := by
  letI : StarRing E := starOf σ hσ
  let h : (Fin n → E) →ₗ⋆[E] (Fin n → E) →ₗ[E] E :=
    LinearMap.mk₂'ₛₗ (starRingEnd E) (RingHom.id E) (hform σ J)
      (fun x x' y => by simp only [hform, Pi.add_apply, map_add (f := _), add_mul, Finset.sum_add_distrib])
      (fun a x y => hform_smul_left σ J a x y)
      (fun x y y' => by simp only [hform, Pi.add_apply, mul_add, Finset.sum_add_distrib])
      (fun a x y => hform_smul_right σ J a x y)
  have hh : ∀ x y, h x y = hform σ J x y := fun _ _ => rfl
  have hsym' : ∀ x y, σ (hform σ J x y) = hform σ J y x := by
    intro x y
    have e : ∀ i j, σ (J i j) = J j i := fun i j => congrFun (congrFun hH j) i

    simp only [hform, map_sum, map_mul, hσ, e]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have hsym : h.IsSymm := ⟨fun x y => hsym' x y⟩
  have hr : ∀ y, (∀ x, hform σ J x y = 0) → y = 0 := by
    intro y hy
    have h1 : J *ᵥ y = 0 := by
      funext i
      have := hy (Pi.single i 1)
      rw [hform_eq, dotProduct, Finset.sum_eq_single i] at this
      · simpa using this
      · intro b _ hb
        simp [hb]
      · simp
    have ey : y = J⁻¹ *ᵥ (J *ᵥ y) := by
      rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul J hJ, Matrix.one_mulVec]
    rw [ey, h1, mulVec_zero]
  have hnd : h.Nondegenerate := by
    refine ⟨fun x hx => hr x fun y => ?_, fun y hy => hr y hy⟩
    rw [← hsym', ← hh, hx y, map_zero]
  have hd : ∀ M : Submodule (𝓞 E) (Fin n → E), Formalism.HermitianLatticesTheory.dual h M = dualL σ J M := by
    intro M
    ext y
    rw [mem_dualL]
    simp only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap, Submodule.mem_one]
    rfl
  have := Formalism.HermitianLatticesTheory.dualLattice (𝓞 E) E (Fin n → E) h hsym hnd (fun r => LocB.sig_int σ r) L hL
  rw [hd, hd] at this
  exact ⟨this.1, this.2.1⟩

theorem localization_dualL_le (σ : E →+* E) (J : Matrix (Fin n) (Fin n) E) (P Q : Ideal (𝓞 E)) [P.IsPrime] [Q.IsPrime]
    (hPQ : ∀ a b : 𝓞 E, (a : E) = σ (b : E) → a ∈ Q → b ∈ P) (M N : Submodule (𝓞 E) (Fin n → E)) (hM : M.FG)
    (h : Formalism.HermitianLatticesTheory.localization₂ P M ≤ Formalism.HermitianLatticesTheory.localization₂ P N) :
    Formalism.HermitianLatticesTheory.localization₂ Q (dualL σ J N) ≤ Formalism.HermitianLatticesTheory.localization₂ Q (dualL σ J M) := by
  have h1P : (1 : 𝓞 E) ∉ P := P.ne_top_iff_one.1 (Ideal.IsPrime.ne_top inferInstance)
  have key : ∃ s : 𝓞 E, s ∉ P ∧ ∀ x ∈ M, s • x ∈ N := by
    have h0 : M ≤ Formalism.HermitianLatticesTheory.localization₂ P N := fun x hx =>
      h ((rlv_mem_locP P M x).2 ⟨1, h1P, by rwa [one_smul]⟩)
    clear h
    induction M, hM using Submodule.fg_induction with
    | singleton x =>
      obtain ⟨s, hs, hx⟩ := (rlv_mem_locP P N x).1 (h0 (Submodule.mem_span_singleton_self x))
      refine ⟨s, hs, fun y hy => ?_⟩
      obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hy
      rw [smul_comm]; exact N.smul_mem a hx
    | sup A B _ _ hA hB =>
      obtain ⟨s, hs, h1⟩ := hA (le_sup_left.trans h0)
      obtain ⟨t, ht, h2⟩ := hB (le_sup_right.trans h0)
      refine ⟨s * t, fun hst => (Ideal.IsPrime.mem_or_mem inferInstance hst).elim hs ht, fun y hy => ?_⟩
      obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hy
      rw [smul_add]
      refine N.add_mem ?_ ?_
      · rw [mul_comm, mul_smul]; exact N.smul_mem _ (h1 a ha)
      · rw [mul_smul]; exact N.smul_mem _ (h2 b hb)
  obtain ⟨s, hs, hsM⟩ := key
  obtain ⟨s', hs'⟩ := LocB.sig_int σ s
  have hs'Q : s' ∉ Q := fun hq => hs (hPQ s' s hs' hq)
  intro y hy
  obtain ⟨t, ht, hty⟩ := (rlv_mem_locP Q _ y).1 hy
  refine (rlv_mem_locP Q _ y).2 ⟨s' * t, fun hst => (Ideal.IsPrime.mem_or_mem inferInstance hst).elim hs'Q ht, ?_⟩
  rw [mem_dualL] at hty ⊢
  intro x hx
  have := hty _ (hsM x hx)
  rw [← algebraMap_smul E s x, hform_smul_left] at this
  rw [mul_smul, ← algebraMap_smul E s' (t • y), hform_smul_right, hs']
  exact this

theorem mem_mulLat (γ : GL (Fin n) E) (L : Submodule (𝓞 E) (Fin n → E)) (y : Fin n → E) :
    y ∈ mulLat γ.1 L ↔ (γ⁻¹).1 *ᵥ y ∈ L := by
  rw [← map_glE, Submodule.mem_map_equiv, glE_symm_apply]

theorem mulLat_lattice (γ : GL (Fin n) E) (L : Submodule (𝓞 E) (Fin n → E)) (hL : Submodule.IsFullLattice E L) :
    Submodule.IsFullLattice E (mulLat γ.1 L) := by
  letI : Submodule.IsLattice E (mulLat γ.1 L) := Submodule.IsLattice.of_fg E (hL.fg.map _)
  constructor
  change Submodule.span E ((L.map ((Matrix.mulVecLin γ.1).restrictScalars (𝓞 E)) :
    Submodule (𝓞 E) (Fin n → E)) : Set (Fin n → E)) = ⊤
  rw [show Submodule.span E ((L.map ((Matrix.mulVecLin γ.1).restrictScalars (𝓞 E)) :
      Submodule (𝓞 E) (Fin n → E)) : Set (Fin n → E)) =
      (Submodule.span E (L : Set (Fin n → E))).map (Matrix.mulVecLin γ.1) by
        rw [Submodule.map_span]; rfl,
    hL.span_eq_top, Submodule.map_top, LinearMap.range_eq_top]
  exact (glE γ).surjective

theorem dualL_mulLat (σ : E →+* E) (J : Matrix (Fin n) (Fin n) E) (γ : GL (Fin n) E) (hγ : γ ∈ UJ σ J)
    (L : Submodule (𝓞 E) (Fin n → E)) : dualL σ J (mulLat γ.1 L) = mulLat γ.1 (dualL σ J L) := by
  ext y
  have ey : γ.1 *ᵥ ((γ⁻¹).1 *ᵥ y) = y := (glE γ).apply_symm_apply y
  rw [mem_mulLat, mem_dualL, mem_dualL]
  constructor
  · intro h x hx
    rw [← hform_unitary σ J γ.1 hγ, ey]
    exact h _ ⟨x, hx, rfl⟩
  · rintro h _ ⟨x, hx, rfl⟩
    have := h x hx
    rw [← hform_unitary σ J γ.1 hγ, ey] at this
    exact this

theorem dual_conj_primes : ∀ (E : Type) [Field E] [NumberField E] (σ : E →+* E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (P Q : Ideal (𝓞 E)) [P.IsPrime] [Q.IsPrime], (∀ x, σ (σ x) = x) → IsUnit J.det → cT σ J = J → (∀ a b : 𝓞 E, (b : E) = σ (a : E) → (a ∈ Q ↔ b ∈ P)) → ∀ M N : Submodule (𝓞 E) (Fin n → E), Submodule.IsFullLattice E M → Submodule.IsFullLattice E N → (Formalism.HermitianLatticesTheory.localization₂ P M = Formalism.HermitianLatticesTheory.localization₂ P N → Formalism.HermitianLatticesTheory.localization₂ Q (dualL σ J M) = Formalism.HermitianLatticesTheory.localization₂ Q (dualL σ J N)) ∧ (Formalism.HermitianLatticesTheory.localization₂ P (dualL σ J M) = Formalism.HermitianLatticesTheory.localization₂ P (dualL σ J N) → Formalism.HermitianLatticesTheory.localization₂ Q M = Formalism.HermitianLatticesTheory.localization₂ Q N) ∧ ∀ γ : GL (Fin n) E, γ ∈ UJ σ J → Submodule.IsFullLattice E (mulLat γ.1 M) ∧ dualL σ J (mulLat γ.1 M) = mulLat γ.1 (dualL σ J M) := by
  intro E _ _ σ n J P Q _ _ hσ hJ hH hPQ M N hM hN
  have hPQ' : ∀ a b : 𝓞 E, (a : E) = σ (b : E) → a ∈ Q → b ∈ P := fun a b hab =>
    (hPQ a b (by rw [hab, hσ])).1
  have one : ∀ A B : Submodule (𝓞 E) (Fin n → E), A.FG → B.FG → Formalism.HermitianLatticesTheory.localization₂ P A = Formalism.HermitianLatticesTheory.localization₂ P B →
      Formalism.HermitianLatticesTheory.localization₂ Q (dualL σ J A) = Formalism.HermitianLatticesTheory.localization₂ Q (dualL σ J B) := fun A B hA hB h =>
    le_antisymm (localization_dualL_le σ J P Q hPQ' B A hB h.ge) (localization_dualL_le σ J P Q hPQ' A B hA h.le)
  obtain ⟨hM1, hM2⟩ := dual_lattice_bidual σ hσ J hJ hH M hM
  obtain ⟨hN1, hN2⟩ := dual_lattice_bidual σ hσ J hJ hH N hN
  refine ⟨one M N hM.fg hN.fg, fun h => ?_, fun γ hγ => ⟨mulLat_lattice γ M hM, dualL_mulLat σ J γ hγ M⟩⟩
  have := one _ _ hM1.fg hN1.fg h
  rwa [hM2, hN2] at this

end GlobalTheory.LevelHecke.DualConj

end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3


theorem _root_.GlobalTheory.T.schur_pairing_invariant_under_standard_group : ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (θ : InfFam D) (M : DSModel V S) (n : ℕ) (P : principalLevelFrame.RowPsi V n) (μ : Measure (GA D V)) (𝓕 : Set (GA D V)), SchurAll D → V.SigOK → IsInfFam θ → μ.IsHaarMeasure → IsFundamentalDomain (GQ V) 𝓕 μ → ∀ (h : Formalism.AUTREP.GAf D.host.E n), ∀ x ∈ principalLevelFrame.Minf θ P M, ∀ y ∈ principalLevelFrame.Minf θ P M, ipM M μ 𝓕 (principalLevelFrame.actM P M h x) (principalLevelFrame.actM P M h y) = ipM M μ 𝓕 x y := by
  exact @GlobalTheory.SchurPairingInvariant.ipM_actM
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.L2.NT Formalism.L2.TwC GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

noncomputable section

namespace GlobalTheory.CycClosure

variable {l : ℕ} [Fact l.Prime]

theorem mem_clC {F : IntermediateField ℚ_[l] (PadicAlgCl l)} {x : ℂ_[l]} :
    x ∈ clC l F ↔ x ∈ closure (algebraMap (PadicAlgCl l) ℂ_[l] '' (F : Set (PadicAlgCl l))) ∧ ‖x‖ ≤ 1 := by
  simp only [clC, Subring.mem_inf]
  apply and_congr Iff.rfl
  change x ∈ PadicComplexInt l ↔ _
  rw [PadicComplexInt, Valuation.mem_valuationSubring_iff, PadicComplex.norm_eq_norm]
  exact (Valued.toNormedField.norm_le_one_iff).symm

theorem coe_clC (F : IntermediateField ℚ_[l] (PadicAlgCl l)) :
    (clC l F : Set ℂ_[l]) =
      closure ((fun y : PadicAlgCl l => (y : ℂ_[l])) '' {y | y ∈ F ∧ ‖y‖ ≤ 1}) := by
  have hc : IsClopen (Metric.closedBall (0 : ℂ_[l]) 1) :=
    IsUltrametricDist.isClopen_closedBall _ one_ne_zero
  have e : (fun y : PadicAlgCl l => (y : ℂ_[l])) '' {y | y ∈ F ∧ ‖y‖ ≤ 1} =
      (algebraMap (PadicAlgCl l) ℂ_[l] '' (F : Set (PadicAlgCl l))) ∩ Metric.closedBall 0 1 := by
    ext x
    constructor
    · rintro ⟨y, ⟨hy, h⟩, rfl⟩
      exact ⟨⟨y, hy, rfl⟩, by rw [mem_closedBall_zero_iff, PadicComplex.norm_extends]; exact h⟩
    · rintro ⟨⟨y, hy, rfl⟩, h⟩
      rw [mem_closedBall_zero_iff] at h
      exact ⟨y, ⟨hy, by rw [← PadicComplex.norm_extends]; exact h⟩, rfl⟩
  rw [e]
  apply Set.Subset.antisymm
  · intro x hx
    rw [SetLike.mem_coe, mem_clC] at hx
    exact hc.isOpen.closure_inter ⟨hx.1, by simpa using hx.2⟩
  · intro x hx
    have := closure_inter_subset_inter_closure _ _ hx
    rw [hc.isClosed.closure_eq] at this
    exact mem_clC.2 ⟨this.1, by simpa using this.2⟩

theorem clC_mono {F G : IntermediateField ℚ_[l] (PadicAlgCl l)} (h : F ≤ G) {x : ℂ_[l]}
    (hx : x ∈ clC l F) : x ∈ clC l G :=
  mem_clC.2 ⟨closure_mono (Set.image_mono h) (mem_clC.1 hx).1, (mem_clC.1 hx).2⟩

theorem clC_props (LL : Loc.FinExt l) (F : IntermediateField ℚ_[l] (PadicAlgCl l))
    (hF : LL.1 ⊔ Loc.MaximalUnramifiedExtension l = F) :
    ∃ _ : IsDiscreteValuationRing ↥(clC l F),
      IsAlgClosed (IsLocalRing.ResidueField ↥(clC l F)) ∧
      IsAdicComplete (IsLocalRing.maximalIdeal ↥(clC l F)) ↥(clC l F) ∧
      IsAdic (IsLocalRing.maximalIdeal ↥(clC l F)) ∧
      (∀ x ∈ clC l F, ∀ y ∈ clC l F, ‖x‖ ≤ ‖y‖ → x / y ∈ clC l F) := by
  subst hF
  obtain ⟨O, hdvr, -, -, hdiv, hres, hcomp, hadic, hO⟩ := GlobalTheory.BigInt.exists_integers_completion l LL
  have e : O = clC l (LL.1 ⊔ Loc.MaximalUnramifiedExtension l) := SetLike.coe_injective (hO.trans (coe_clC _).symm)
  subst e
  exact ⟨hdvr, hres, hcomp, hadic, hdiv⟩

theorem muK_spec (k : ℕ) : FiniteDimensional ℚ_[l] ↥(muK l k) ∧
    ∃ ζ : PadicAlgCl l, IsPrimitiveRoot ζ (l ^ k) ∧ muK l k = IntermediateField.adjoin ℚ_[l] {ζ} := by
  have hn : 0 < l ^ k := pow_pos (Fact.out : l.Prime).pos k
  haveI : NeZero (l ^ k) := ⟨hn.ne'⟩
  classical
  have hfin : ({x | x ^ (l ^ k) = 1} : Set (PadicAlgCl l)).Finite := by
    refine (Polynomial.nthRoots (l ^ k) (1 : PadicAlgCl l)).toFinset.finite_toSet.subset fun x hx => ?_
    simp only [Finset.mem_coe, Multiset.mem_toFinset, Polynomial.mem_nthRoots hn]
    exact hx
  haveI := hfin.to_subtype
  refine ⟨IntermediateField.finiteDimensional_adjoin fun x hx =>
    ⟨X ^ (l ^ k) - C 1, monic_X_pow_sub_C 1 hn.ne', by simp [show x ^ (l ^ k) = 1 from hx]⟩, ?_⟩
  have hdeg : (cyclotomic (l ^ k) (PadicAlgCl l)).degree ≠ 0 := by
    rw [degree_cyclotomic]; exact_mod_cast (Nat.totient_pos.2 hn).ne'
  obtain ⟨ζ, hζ⟩ := IsAlgClosed.exists_root _ hdeg
  have hp : IsPrimitiveRoot ζ (l ^ k) := (isRoot_cyclotomic_iff).1 hζ
  refine ⟨ζ, hp, le_antisymm ?_ ?_⟩
  · rw [muK, IntermediateField.adjoin_le_iff]
    intro x hx
    have hx' : x ^ (l ^ k) = 1 := hx
    obtain ⟨i, -, rfl⟩ := hp.eq_pow_of_pow_eq_one hx'
    exact pow_mem (IntermediateField.mem_adjoin_simple_self ℚ_[l] ζ) _
  · rw [IntermediateField.adjoin_le_iff, Set.singleton_subset_iff]
    exact IntermediateField.subset_adjoin _ _ hp.pow_eq_one

end GlobalTheory.CycClosure

namespace GlobalTheory.CycClosure

theorem exists_cyclotomic_integers : ∀ (l : ℕ) [Fact l.Prime] (K₀ L : Loc.FinExt l) (k : ℕ), ∃ _ : IsDiscreteValuationRing ↥(clC l (Kt l K₀ L ⊔ muK l k)), IsAlgClosed (IsLocalRing.ResidueField ↥(clC l (Kt l K₀ L ⊔ muK l k))) ∧ IsAdicComplete (IsLocalRing.maximalIdeal ↥(clC l (Kt l K₀ L ⊔ muK l k))) ↥(clC l (Kt l K₀ L ⊔ muK l k)) ∧ IsAdic (IsLocalRing.maximalIdeal ↥(clC l (Kt l K₀ L ⊔ muK l k))) ∧ (∀ x ∈ clC l (Kt l K₀ L ⊔ muK l k), ∀ y ∈ clC l (Kt l K₀ L ⊔ muK l k), ‖x‖ ≤ ‖y‖ → x / y ∈ clC l (Kt l K₀ L ⊔ muK l k)) ∧ muK l 0 = ⊥ ∧ (∃ T : Finset ℂ_[l], ∀ x, x ∈ clC l (Kt l K₀ L ⊔ muK l k) ↔ x ∈ Submodule.span ↥(clC l (Kt l K₀ L)) (T : Set ℂ_[l])) ∧ ∃ ζ ∈ clC l (Kt l K₀ L ⊔ muK l k), IsPrimitiveRoot ζ (l ^ k) ∧ ∀ x ∈ clC l (Kt l K₀ L ⊔ muK l k), ∃ (p : Polynomial ↥(clC l (Kt l K₀ L))) (d : ↥(clC l (Kt l K₀ L))), d ≠ 0 ∧ x * (d : ℂ_[l]) = Polynomial.aeval ζ p := by
  intro l _ K₀ L k
  have hp : l.Prime := Fact.out
  obtain ⟨hfd, ζ, hζ, hmu⟩ := muK_spec (l := l) k
  let LL : Loc.FinExt l := ⟨K₀.1 ⊔ L.1 ⊔ muK l k, by haveI := K₀.2; haveI := L.2; infer_instance⟩
  have hM : LL.1 ⊔ Loc.MaximalUnramifiedExtension l = Kt l K₀ L ⊔ muK l k := by
    simp only [LL, Kt]; exact sup_right_comm _ _ _
  let L0 : Loc.FinExt l := ⟨K₀.1 ⊔ L.1, by haveI := K₀.2; haveI := L.2; infer_instance⟩
  obtain ⟨hdvr, hres, hcomp, hadic, hdiv⟩ := clC_props LL _ hM
  obtain ⟨hdvr0, -, -, -, -⟩ := clC_props L0 (Kt l K₀ L) rfl
  have mu0 : muK l 0 = ⊥ := by
    rw [muK, eq_bot_iff, IntermediateField.adjoin_le_iff]
    intro x hx
    have : x = 1 := by simpa using hx
    rw [this]; exact one_mem _
  have hn : 0 < l ^ k := pow_pos hp.pos k
  have hint : IsIntegral ℚ_[l] ζ :=
    ⟨X ^ (l ^ k) - C 1, monic_X_pow_sub_C 1 hn.ne', by simp [hζ.pow_eq_one]⟩
  obtain ⟨n, Cb, hC⟩ := GlobalTheory.T.exists_coeff_bounded_in_closure_of_norm_le_one l (Kt l K₀ L) ζ hint
  have hB : ∀ x, x ∈ clC l (Kt l K₀ L ⊔ muK l k) ↔ x ∈ clC l (Kt l K₀ L ⊔ IntermediateField.adjoin ℚ_[l] {ζ}) := by
    intro x; rw [hmu]
  have hl : ‖(l : ℂ_[l])‖ < 1 := by
    rw [← map_natCast (algebraMap (PadicAlgCl l) ℂ_[l])]
    refine lt_of_eq_of_lt (PadicComplex.norm_extends l (l : PadicAlgCl l)) ?_
    rw [GlobalTheory.UnramValue.norm_l]
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.one_lt)
  have hl0 : (l : ℂ_[l]) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (show (0 : ℝ) < 1 / (max Cb 1) by positivity) hl
  have cmem : ∀ c ∈ closure (algebraMap (PadicAlgCl l) ℂ_[l] '' ((Kt l K₀ L : IntermediateField ℚ_[l] (PadicAlgCl l)) : Set (PadicAlgCl l))),
      ‖c‖ ≤ Cb → (l : ℂ_[l]) ^ N * c ∈ clC l (Kt l K₀ L) := by
    intro c hc hcb
    refine mem_clC.2 ⟨map_mem_closure (continuous_const.mul continuous_id) hc ?_, ?_⟩
    · rintro _ ⟨z, hz, rfl⟩
      refine ⟨(l : PadicAlgCl l) ^ N * z, mul_mem (pow_mem (natCast_mem _ _) _) hz, ?_⟩
      simp
    · rw [norm_mul, norm_pow]
      have h1 : ‖c‖ ≤ max Cb 1 := hcb.trans (le_max_left _ _)
      have h2 : (0 : ℝ) < max Cb 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
      calc ‖(l : ℂ_[l])‖ ^ N * ‖c‖ ≤ ‖(l : ℂ_[l])‖ ^ N * max Cb 1 :=
            mul_le_mul_of_nonneg_left h1 (by positivity)
        _ ≤ 1 / max Cb 1 * max Cb 1 := mul_le_mul_of_nonneg_right hN.le h2.le
        _ = 1 := by field_simp
  set ζ' : ℂ_[l] := algebraMap (PadicAlgCl l) ℂ_[l] ζ with hζ'
  have hζn : ‖ζ‖ = 1 := by
    have := congrArg norm hζ.pow_eq_one
    rw [norm_pow, norm_one] at this
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn.ne').1 this
  have hζB : ζ' ∈ clC l (Kt l K₀ L ⊔ muK l k) := by
    rw [hB]
    refine mem_clC.2 ⟨subset_closure ⟨ζ, (le_sup_right : IntermediateField.adjoin ℚ_[l] {ζ} ≤ _)
      (IntermediateField.mem_adjoin_simple_self ℚ_[l] ζ), rfl⟩, ?_⟩
    exact ((PadicComplex.norm_extends l ζ).trans hζn).le
  have hAB : ∀ x ∈ clC l (Kt l K₀ L), x ∈ clC l (Kt l K₀ L ⊔ muK l k) := fun x hx => clC_mono le_sup_left hx
  have hlN : (l : ℂ_[l]) ^ N ∈ clC l (Kt l K₀ L) := pow_mem (natCast_mem _ _) _
  have rep : ∀ x ∈ clC l (Kt l K₀ L ⊔ muK l k), ∃ c : Fin n → ℂ_[l],
      (∀ i, (l : ℂ_[l]) ^ N * c i ∈ clC l (Kt l K₀ L)) ∧ x = ∑ i, c i * ζ' ^ (i : ℕ) := by
    intro x hx
    rw [hB] at hx
    obtain ⟨c, hc, e⟩ := hC x (mem_clC.1 hx).1 (mem_clC.1 hx).2
    exact ⟨c, fun i => cmem _ (hc i).1 (hc i).2, e⟩
  refine ⟨hdvr, hres, hcomp, hadic, hdiv, mu0, ?_, ζ', hζB, hζ.map_of_injective (algebraMap (PadicAlgCl l) ℂ_[l]).injective, ?_⟩
  · classical
    let g : Fin n → ℂ_[l] := fun i => ((l : ℂ_[l]) ^ N)⁻¹ * ζ' ^ (i : ℕ)
    let P : Submodule ↥(clC l (Kt l K₀ L)) ℂ_[l] := Submodule.span ↥(clC l (Kt l K₀ L)) (Set.range g)
    let B' : Submodule ↥(clC l (Kt l K₀ L)) ℂ_[l] :=
      { carrier := (clC l (Kt l K₀ L ⊔ muK l k) : Set ℂ_[l])
        add_mem' := fun ha hb => add_mem ha hb
        zero_mem' := zero_mem _
        smul_mem' := fun a x hx => by
          rw [Subring.smul_def, smul_eq_mul]
          exact mul_mem (hAB _ a.2) hx }
    have hBP : B' ≤ P := by
      intro x hx
      obtain ⟨c, hc, rfl⟩ := rep x hx
      refine Submodule.sum_mem _ fun i _ => ?_
      have := Submodule.smul_mem P (⟨(l : ℂ_[l]) ^ N * c i, hc i⟩ : ↥(clC l (Kt l K₀ L)))
        (Submodule.subset_span ⟨i, rfl⟩ : g i ∈ P)
      convert this using 1
      rw [Subring.smul_def, smul_eq_mul]
      change c i * ζ' ^ (i : ℕ) = ((l : ℂ_[l]) ^ N * c i) * (((l : ℂ_[l]) ^ N)⁻¹ * ζ' ^ (i : ℕ))
      field_simp
    haveI : IsNoetherian ↥(clC l (Kt l K₀ L)) ↥P :=
      isNoetherian_of_fg_of_noetherian P (Submodule.fg_span (Set.finite_range g))
    have hfg : B'.FG := by
      have h1 : (B'.comap P.subtype).FG := IsNoetherian.noetherian _
      have h2 := h1.map P.subtype
      rwa [Submodule.map_comap_subtype, inf_eq_right.2 hBP] at h2
    obtain ⟨T, hT⟩ := hfg
    exact ⟨T, fun x => by rw [hT]; rfl⟩
  · intro x hx
    obtain ⟨c, hc, rfl⟩ := rep x hx
    refine ⟨∑ i : Fin n, monomial (i : ℕ) (⟨(l : ℂ_[l]) ^ N * c i, hc i⟩ : ↥(clC l (Kt l K₀ L))),
      ⟨(l : ℂ_[l]) ^ N, hlN⟩, fun h => pow_ne_zero N hl0 (congrArg Subtype.val h), ?_⟩

    simp only [map_sum, aeval_monomial, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    change c i * ζ' ^ (i : ℕ) * (l : ℂ_[l]) ^ N = ((l : ℂ_[l]) ^ N * c i) * ζ' ^ (i : ℕ)
    ring

end GlobalTheory.CycClosure
end
end
