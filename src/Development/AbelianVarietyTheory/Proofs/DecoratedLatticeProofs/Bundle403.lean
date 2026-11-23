module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle024
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemHomLatticeCompletionIffSupportedMaps
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualSplitComponentIsLatticeStabilizerEq
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ParahoricLevelsCharactersDoubleCosetsAgreeRation
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle054
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StandardCharacterConductorAlmostAll
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle067
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle002
import Formalism.LocalToGlobal.ProjectiveLattices.HostInt
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsUnitarySupportedAtPlaceOfMulEqIdem
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PlacesToAdeles
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FourierJacobiBesselFlatMapFactorIsLocalModel
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle370
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle372
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle373
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle022
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.JointSmooth
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiStarOfMid
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle019
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.UnitRatio
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle076

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.LatPair GlobalTheory.SeeSaw GlobalTheory.FinPl ValuativeRel
open scoped TensorProduct nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SeeSaw.AdaptFBIdeals

variable {D : D7}

theorem supp_of_colMul {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (L : Lat S) (v : Pl D) (i : Fin ρ) (a : AE D)
    (h : colMul d.jX i a ∈ latV S L (· = v)) : a ∈ idAt D (· = v) := by
  have hp : d.pX * d.jX = 1 := by
    have h := congrArg rat d.e'e
    rw [rat_one] at h
    simpa only [HypDec.pX, HypDec.qX, HypDec.jX, rat, Matrix.map_mul] using h
  have h1 : (d.pX * d.jX) i i = 1 := by rw [hp]; exact Matrix.one_apply_eq i
  rw [Matrix.mul_apply] at h1
  have h2 : a = ∑ k, d.pX i k * colMul d.jX i a k := by
    calc a = a * ∑ k, d.pX i k * d.jX k i := by rw [h1, mul_one]
      _ = _ := by rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun k _ => ?_; simp only [colMul]; ring
  rw [h2]
  exact Ideal.sum_mem _ fun k _ => Ideal.mul_mem_left _ _ (GlobalTheory.FinPl.FrameLat.latV_supp h k)

theorem idV_supp (𝔞 : FI D) (v : Pl D) {a : AE D} (h : a ∈ idV 𝔞 v) : a ∈ idAt D (· = v) := by
  induction h using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨α, -, hα, x, -, rfl⟩ := hy
    exact GlobalTheory.FinPl.LatMem.tmul_mem_idAt hα _
  | zero => exact zero_mem _
  | add x y _ _ hx hy => exact add_mem hx hy
  | neg x _ hx => exact neg_mem hx

end GlobalTheory.SeeSaw.AdaptFBIdeals

namespace GlobalTheory.SeeSaw

end GlobalTheory.SeeSaw
end
end

section

open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.TwBridge
open GlobalTheory.SymBridge (toLoc IsOrd yPos xPos IsCompl)

noncomputable section
namespace GlobalTheory.TwBridge.LevOrb
open GlobalTheory.TwBridge.Lev

theorem inX_zero {E : Type} [Field E] (n : ℕ) (x : Fin n → E) : Loc.inX E n 0 x = x := by
  funext l
  simp [Loc.inX, show l.1 < n from l.2]

theorem mem_prX_zero {E : Type} [Field E] {n : ℕ} (J : Subgroup ((Fin (n + 0) → E) ≃ₗ[E] (Fin (n + 0) → E)))
    (κ : (Fin n → E) ≃ₗ[E] (Fin n → E)) : κ ∈ Loc.prX (Loc.Cbe J 1) ↔ (show (Fin (n + 0) → E) ≃ₗ[E] (Fin (n + 0) → E) from κ) ∈ J := by
  have hR : ∀ γ : (Fin (n + 0) → E) ≃ₗ[E] (Fin (n + 0) → E), Loc.R1cond E n 0 γ := fun γ => by
    rw [r1cond_iff]
    intro l l' h
    have := l.2
    have := l'.2
    omega
  constructor
  · rintro ⟨r, hr, hx⟩
    have h2 : r ∈ J := by simpa [MulAut.conj_apply] using hr.2
    have : r = κ := LinearEquiv.ext fun x => by simpa only [inX_zero] using hx x
    exact this ▸ h2
  · intro h
    refine ⟨κ, ⟨⟨hR _, hR _⟩, ?_⟩, fun x => by rw [inX_zero, inX_zero]⟩
    simpa [MulAut.conj_apply] using h

section Orb
variable {E k : Type} [Field E] [NumberField E] [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {P : HeightOneSpectrum (𝓞 E)} {q : ℕ} {ι : E →+* k} {ϖ : kˣ} {A : Type} [Fintype A] [DecidableEq A] {n : ℕ}

omit [Fintype A] [DecidableEq A] in
theorem mem_box_iff (hc : IsCompl P q ι ϖ) (e : A ≃ Fin n) (M : ℕ) (v : Sp E n) :
    (fun r => ι (v (e r))) ∈ box A (ϖ ^ M) ↔ ((q : E) ^ M)⁻¹ • v ∈ stdAt E n P := by
  rw [stdAt, StabRef.mem_locStd, mem_box]
  have key : ∀ a : E, valuation k (ι a) ≤ valuation k ((ϖ ^ M : kˣ) : k) ↔ IntAt P (((q : E) ^ M)⁻¹ * a) := fun a => by
    rw [← hc.int, map_mul, map_inv₀, map_pow, ← hc.unif, Valuation.mem_integer_iff, map_mul, map_inv₀, Units.val_pow_eq_pow_val,
      inv_mul_le_iff₀ (zero_lt_iff.2 (by simp)), mul_one]
  refine ⟨fun h l => ?_, fun h r => (key _).2 (h (e r))⟩
  obtain ⟨r, rfl⟩ := e.surjective l
  exact (key _).1 (h r)

omit [NumberField E] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem phi_mulVec (e : A ≃ Fin n) (e' : A ⊕ Fin 0 ≃ Fin n) (he : ∀ a, e' (.inl a) = e a) (γ : (Fin n → E) ≃ₗ[E] (Fin n → E))
    (z : Fin n → E) : (phi ι e' γ).val.toBlocks₁₁ *ᵥ (fun r => ι (z (e r))) = fun r => ι (γ z (e r)) := by
  funext r

  rw [apply_sum γ z, map_sum, ← e.sum_comp]
  simp [mulVec, dotProduct, toBlocks₁₁, phi_val, toLoc, he]

theorem mulVec_mem_box {g : GL (A ⊕ Fin 0) k} (hg : g ∈ KO k _) (a : kˣ) {y : A → k} (hy : y ∈ box A a) :
    g.val.toBlocks₁₁ *ᵥ y ∈ box A a := fun i => by
  refine Valuation.map_sum_le _ fun j _ => ?_
  rw [map_mul]
  exact mul_le_of_le_one_of_le ((mem_KO.1 hg).1 (Sum.inl i) (Sum.inl j)) (hy j)

theorem sameOrb_iff (hc : IsCompl P q ι ϖ) (e : A ≃ Fin n) (e' : A ⊕ Fin 0 ≃ Fin n) (he : ∀ a, e' (.inl a) = e a)
    (J : Subgroup (GL (A ⊕ Fin 0) k)) (h1 : KOne k _ ≤ J) (h2 : J ≤ KO k _) (M : ℕ) (z z' : Sp E n) :
    GlobalTheory.QPl.SameOrb J (box _ (ϖ ^ M)) (Submodule.Quotient.mk fun r => ι (z (e r))) (Submodule.Quotient.mk fun r => ι (z' (e r))) ↔
      ∃ γ : Sp E n ≃ₗ[E] Sp E n, phi ι e' γ ∈ J ∧ ((q : E) ^ M)⁻¹ • (γ z - z') ∈ stdAt E n P := by
  have hsub : ∀ γ : Sp E n ≃ₗ[E] Sp E n, (phi ι e' γ).val.toBlocks₁₁ *ᵥ (fun r => ι (z (e r))) - (fun r => ι (z' (e r))) =
      fun r => ι ((γ z - z') (e r)) := fun γ => by
    rw [phi_mulVec e e' he]
    funext r
    simp
  constructor
  · rintro ⟨g, hg, y, hy, hy'⟩
    rw [Submodule.Quotient.eq] at hy hy'
    have h0 : g.val.toBlocks₁₁ *ᵥ (fun r => ι (z (e r))) - (fun r => ι (z' (e r))) ∈ box A (ϖ ^ M) := by
      have := sub_mem hy' (mulVec_mem_box (h2 hg) _ hy)
      rw [mulVec_sub] at this
      convert this using 1
      abel
    have hU1 : IsOpen {N : Matrix (A ⊕ Fin 0) (A ⊕ Fin 0) k | MaxM ((g⁻¹).val * N - 1)} := by
      simp only [MaxM, Set.setOf_forall]
      refine isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => ?_
      exact IsOpen.preimage (f := fun N : Matrix (A ⊕ Fin 0) (A ⊕ Fin 0) k => ((g⁻¹).val * N - 1) i j)
        (t := {z | valuation k z < 1}) (by fun_prop) (by simpa using (valuation k).isOpen_ball 1)
    have ho : IsOpen ((box A (ϖ ^ M) : Submodule 𝒪[k] (A → k)) : Set (A → k)) := by
      convert (isOpen_set_pi Set.finite_univ fun (_ : A) _ => isOpen_cball (ϖ ^ M)) using 1
      ext z; simp [mem_box, cball]
    have hU2 : IsOpen {N : Matrix (A ⊕ Fin 0) (A ⊕ Fin 0) k |
        N.toBlocks₁₁ *ᵥ (fun r => ι (z (e r))) - (fun r => ι (z' (e r))) ∈ box A (ϖ ^ M)} := by
      refine ho.preimage (f := fun N : Matrix (A ⊕ Fin 0) (A ⊕ Fin 0) k =>
        N.toBlocks₁₁ *ᵥ (fun r => ι (z (e r))) - (fun r => ι (z' (e r)))) ?_
      have hb : Continuous fun N : Matrix (A ⊕ Fin 0) (A ⊕ Fin 0) k => N.toBlocks₁₁ :=
        continuous_pi fun i => continuous_pi fun j => continuous_apply_apply (Sum.inl i) (Sum.inl j)
      exact (hb.matrix_mulVec continuous_const).sub continuous_const
    obtain ⟨M₀, ⟨a1, a2⟩, -⟩ := exists_approx ι hc.dense g.val (hU1.inter hU2) ⟨by
      change MaxM _
      rw [Units.inv_mul, sub_self]
      exact maxM_zero, h0⟩
    obtain ⟨u, hu, eu⟩ := exists_mem_KOne a1
    have ev : (g * u).val = M₀.map ι := by
      rw [Units.val_mul, eu, ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]
    obtain ⟨γ, hγ⟩ := exists_phi ι e' M₀ _ ev
    refine ⟨γ, hγ ▸ mul_mem hg (h1 hu), (mem_box_iff hc e M _).1 ?_⟩
    rw [← hsub, hγ, ev]
    exact a2
  · rintro ⟨γ, hγ, h⟩
    refine ⟨_, hγ, _, rfl, (Submodule.Quotient.eq _).2 ?_⟩
    rw [hsub]
    exact (mem_box_iff hc e M _).2 h

end Orb

theorem mem_prX_JQ {E : Type} [Field E] [NumberField E] [StarRing E] (P : HeightOneSpectrum (𝓞 E)) (q kj n c : ℕ) (hc : c = 0)
    (κ : Sp E n ≃ₗ[E] Sp E n) : κ ∈ Loc.prX (Loc.Cbe (LocE.JQ P q kj n c) 1) ↔
      (show Sp E (n + 0) ≃ₗ[E] Sp E (n + 0) from κ) ∈ LocE.JQ P q kj n 0 := by
  subst hc
  exact mem_prX_zero _ κ

theorem sameOrb_iff_level : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S₀ : Set ℕ) (mu : Tup X.F X.E X.K S₀) (cst : LocCst X (rowSG Pr sel mu)) (σ₀ : X.K →+* ℂ) (P : rowSG Pr sel mu) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : X.E →+* k) (s : ℕ) (W : TwData k), AtTwist (R := R) sel mu cst σ₀ P ι s W → ∀ (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (G : ChGlob X R.m), L.Ok Ch sel mu cst G s → ∀ (b : L.β (s + 1)) (hQ : P.1 ∈ QE sel (mu : Chr X.F X.E X.K)) (e : XIx (Fin R.k) (Fin R.t) (s + 1) ≃ Fin (R.N (s + 1))), GlobalTheory.SymBridge.IsOrd GlobalTheory.SymBridge.xPos e → ∀ z z' : Sp X.E (R.N (s + 1)), (GlobalTheory.QPl.SameOrb ((W.T s R).lev (s + 1) 0 rfl).J (box _ (W.ϖ ^ cst.M)) (Submodule.Quotient.mk fun r => ι (z (e r))) (Submodule.Quotient.mk fun r => ι (z' (e r))) ↔ ∃ κ ∈ (L.levQ (s + 1) b ⟨P.1, hQ⟩).H, ((qOf P.1 : X.E) ^ cst.M)⁻¹ • (κ.1 z - z') ∈ stdAt X.E (R.N (s + 1)) P.1) := by
  intro X Pr R Ch sel S₀ mu cst σ₀ P k _ _ _ _ ι s W hA L G hL b hQ e he z z'
  have hc : cOf R (s + 1) = 0 := by have := hA.steps; unfold cOf; omega
  have hn : R.N (s + 1) = R.k + (s + 1) * (R.t + 1) := rfl
  let e' : XIx (Fin R.k) (Fin R.t) (s + 1) ⊕ Fin 0 ≃ Fin (R.N (s + 1) + 0) := (Equiv.sumEmpty _ _).trans e
  have he' : IsOrd (yPos xPos (R.N (s + 1))) e' := by
    rintro (a | a)
    · exact he a
    · exact a.elim0
  set o := stdOrd (Fin R.k) (Fin R.t) (s + 1) 0 (rfl : s + 1 + 0 = s + 1) with ho
  have hconj : ∀ g : GL _ k, (plainFrame (k := k) o).conj.symm g = (reGL o).symm g := fun g => by
    rw [MulEquiv.symm_apply_eq, LatFrame.conj_apply, show (plainFrame (k := k) o).bas = 1 from rfl,
      show (plainFrame (k := k) o).ord = o from rfl, MulEquiv.apply_symm_apply]
    simp
  have hJ : ∀ g, g ∈ ((W.T s R).lev (s + 1) 0 rfl).J ↔ (reGL o).symm g ∈ (parahoric _ (Fin (s + 1) × Fin R.t) W.δ W.tame).J :=
    fun g => by rw [← hconj]; rfl
  have hmem : ∀ γ : Sp X.E (R.N (s + 1)) ≃ₗ[X.E] Sp X.E (R.N (s + 1)), phi ι e' γ ∈ ((W.T s R).lev (s + 1) 0 rfl).J ↔
      γ ∈ prCat (Pr := Pr) cst.sharp (s + 1) P.1 (L.h (s + 1) b P) := fun γ => by
    rw [hJ, hL.last_h, prCat, Jat, if_neg hA.nmem, mem_prX_JQ _ _ _ _ _ hc]
    exact mem_par_iff (c := 0) (s := s) hA.compl W.unif rfl hn he' W.tame γ
  have hle : ((W.T s R).lev (s + 1) 0 rfl).J ≤ KO k _ := fun g hg => by
    have h := (mem_parahoric.1 ((hJ g).1 hg)).1
    rw [mem_KO] at h ⊢
    rw [← map_inv] at h
    refine ⟨fun i j => ?_, fun i j => ?_⟩
    · simpa [reGL_symm_val] using h.1 (o.symm i) (o.symm j)
    · simpa [reGL_symm_val] using h.2 (o.symm i) (o.symm j)
  rw [sameOrb_iff hA.compl e e' (fun _ => rfl) _
    (fun u hu => (hJ u).2 (((parahoric _ (Fin (s + 1) × Fin R.t) W.δ W.tame).reindex o).KOne_le hu)) hle, hL.grpQ]
  constructor
  · rintro ⟨γ, h1, h2⟩
    have h3 := (hmem γ).1 h1
    exact ⟨⟨γ, hL.int _ b P h3⟩, h3, h2⟩
  · rintro ⟨κ, h1, h2⟩
    exact ⟨κ.1, (hmem _).2 h1, h2⟩

end GlobalTheory.TwBridge.LevOrb
end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.LatPair GlobalTheory.SeeSaw GlobalTheory.FinPl ValuativeRel
open scoped TensorProduct nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SeeSaw.DiffDual

variable {D : D7}

def TrInt (D : D7) (x : D.host.E) : Prop := ∀ o : 𝓞 D.host.E, ∃ n : ℤ, Algebra.trace ℚ D.host.E (x * o) = n

theorem mem_dI_iff (x : D.host.E) : x ∈ dI D ↔ TrInt D x := by
  rw [dI, Formalism.L2.Pj.dual_eq Formalism.IndefR.Fin.factPrincipalDatum D,
    FractionalIdeal.mem_dual (@one_ne_zero (FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) _ _ _)]
  constructor
  · intro h o
    obtain ⟨n, hn⟩ := h _ ((FractionalIdeal.mem_one_iff _).2 ⟨o, rfl⟩)
    refine ⟨n, ?_⟩
    rw [Algebra.traceForm_apply] at hn
    rw [← hn]; simp
  · intro h b hb
    obtain ⟨o, rfl⟩ := (FractionalIdeal.mem_one_iff _).1 hb
    obtain ⟨n, hn⟩ := h o
    refine ⟨n, ?_⟩
    rw [Algebra.traceForm_apply]
    rw [show algebraMap (𝓞 D.host.E) D.host.E o = (o : D.host.E) from rfl, hn]; simp

theorem TrInt.mul {x : D.host.E} (h : TrInt D x) (o : 𝓞 D.host.E) : TrInt D (x * o) := fun o' => by
  obtain ⟨n, hn⟩ := h (o * o')
  exact ⟨n, by rw [mul_assoc]; simpa using hn⟩

theorem trInt_coe (o : 𝓞 D.host.E) : TrInt D (o : D.host.E) := fun o' => by
  have hi : IsIntegral ℤ ((o : D.host.E) * o') := o.isIntegral_coe.mul o'.isIntegral_coe
  obtain ⟨n, hn⟩ := IsIntegrallyClosed.isIntegral_iff.1 (Algebra.isIntegral_trace (L := ℚ) hi)
  exact ⟨n, hn.symm⟩

theorem chi_tmul {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {β : Af D.host.F}
    (hβ : β ∈ intAf D.host.F) {x : D.host.E} (hx : TrInt D x) : Conductor.chi ψ (β ⊗ₜ[D.host.F] x) = 1 := by
  rw [Conductor.chi, GlobalTheory.LatVac.trace_tmul]
  refine GlobalTheory.IntDense.addChar_eq_one_of_integral D.host.F ψ hψ.1.1 _ (fun a => ?_) _ hβ
  rw [← smul_eq_mul, ← map_smul, GlobalTheory.LatVac.char_rat hψ]
  have hi : IsIntegral ℤ (algebraMap D.host.F D.host.E (a : D.host.F)) :=
    a.isIntegral_coe.map (IsScalarTower.toAlgHom ℤ D.host.F D.host.E)
  obtain ⟨n, hn⟩ := hx ⟨_, hi⟩
  exact ⟨n, by rw [Algebra.smul_def, mul_comm]; exact hn⟩

theorem chi_mul_int {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {x : D.host.E} (hx : TrInt D x)
    {z : Af D.host.F ⊗[D.host.F] D.host.E} (hz : z ∈ intAE D) :
    Conductor.chi ψ (((1 : Af D.host.F) ⊗ₜ[D.host.F] x) * z) = 1 := by
  induction hz using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨β, hβ, o, rfl⟩ := hw
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    exact chi_tmul hψ hβ (hx.mul o)
  | zero => rw [mul_zero]; exact Conductor.chi_zero ψ
  | add y y' _ _ hy hy' => rw [mul_add, Conductor.chi_add, hy, hy', one_mul]
  | neg y _ hy =>
    have := Conductor.chi_add ψ (((1 : Af D.host.F) ⊗ₜ[D.host.F] x) * y) (((1 : Af D.host.F) ⊗ₜ[D.host.F] x) * -y)
    rwa [← mul_add, add_neg_cancel, mul_zero, Conductor.chi_zero, hy, one_mul, eq_comm] at this

theorem psiE_add (ψ : AddChar (AF D.host.F) ℂ) (a b : AE D) : psiE ψ (a + b) = psiE ψ a * psiE ψ b := by
  rw [psiE, psiE, psiE, map_add (f := _), ψ.map_add_eq_mul]

theorem psiE_zero (ψ : AddChar (AF D.host.F) ℂ) : psiE ψ (0 : AE D) = 1 := by
  rw [psiE, map_zero, ψ.map_zero_eq_one]

theorem psiE_neg (ψ : AddChar (AF D.host.F) ℂ) (a : AE D) : psiE ψ (-a) = (psiE ψ a)⁻¹ := by
  rw [psiE, psiE, map_neg, ψ.map_neg_eq_inv]

theorem forward {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (v : Pl D) {s : AE D}
    (hs : s ∈ idV (dI D) v) : ∀ o ∈ intAt D (· = v), psiE ψ (s * o) = 1 := by
  induction hs using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨α, hα, -, a, ha, rfl⟩ := hy
    intro o ho
    have hinf : infPart D (pairA D.host.F 0 α ⊗ₜ[D.host.F] a * o) = 0 := by
      rw [RingHom.map_mul, GlobalTheory.LatVac.infPart_pair, zero_mul]
    rw [Conductor.psiE_eq_chi ψ hinf, RingHom.map_mul, GlobalTheory.LatVac.finPart_pair]
    have e : α ⊗ₜ[D.host.F] a = ((1 : Af D.host.F) ⊗ₜ[D.host.F] a) * (α ⊗ₜ[D.host.F] (1 : D.host.E)) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
    rw [e, mul_assoc]
    exact chi_mul_int hψ ((mem_dI_iff a).1 ha) (Conductor.mul_mem_int (Conductor.tmul_mem hα 1) ho.2)
  | zero => intro o _; rw [zero_mul, psiE_zero]
  | add x y _ _ hx hy => intro o ho; rw [add_mul, psiE_add, hx o ho, hy o ho, one_mul]
  | neg x _ hx => intro o ho; rw [neg_mul, psiE_neg, hx o ho, inv_one]

def lift (D : D7) : Af D.host.F ⊗[D.host.F] D.host.E →ₗ[D.host.F] AE D :=
  (LinearMap.inr D.host.F (Ainf D.host.F) (Af D.host.F)).rTensor D.host.E

theorem lift_tmul (α : Af D.host.F) (x : D.host.E) : lift D (α ⊗ₜ[D.host.F] x) = pairA D.host.F 0 α ⊗ₜ[D.host.F] x := rfl

theorem finPart_lift (z : Af D.host.F ⊗[D.host.F] D.host.E) : finPart D (lift D z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul α x => rw [lift_tmul, GlobalTheory.LatVac.finPart_pair]
  | add x y hx hy => rw [LinearMap.map_add (f := _), RingHom.map_add (f := _), hx, hy]

theorem infPart_lift (z : Af D.host.F ⊗[D.host.F] D.host.E) : infPart D (lift D z) = 0 := by
  induction z using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul α x => rw [lift_tmul, GlobalTheory.LatVac.infPart_pair]
  | add x y hx hy => rw [LinearMap.map_add (f := _), RingHom.map_add (f := _), hx, hy, add_zero]

theorem eq_lift {s : AE D} (h : infPart D s = 0) : s = lift D (finPart D s) := by
  rw [← sub_eq_zero]
  refine GlobalTheory.LatVac.eq_zero_of_parts _ ?_ ?_
  · rw [RingHom.map_sub, h, infPart_lift, sub_zero]
  · rw [RingHom.map_sub, finPart_lift, sub_self]

theorem lift_int_mem (v : Pl D) (hε : singleV D.host.F v 1 ∈ intAf D.host.F) {u : Af D.host.F ⊗[D.host.F] D.host.E}
    (hu : u ∈ intAE D) : lift D ((singleV D.host.F v 1 ⊗ₜ[D.host.F] (1 : D.host.E)) * u) ∈ idV (dI D) v := by
  induction hu using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨β, hβ, o, rfl⟩ := hy
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    refine AddSubgroup.subset_closure ⟨_, GlobalTheory.LatVac.mul_mem_intAf hε hβ, fun w hw => ?_, (o : D.host.E),
      (mem_dI_iff _).2 (trInt_coe o), lift_tmul _ _⟩
    rw [map_mul, Conductor.ev_ne hw, zero_mul]
  | zero => rw [mul_zero, map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [mul_add, map_add (f := _)]; exact add_mem hx hy
  | neg x _ hx => rw [mul_neg, map_neg]; exact neg_mem hx

theorem backward {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (v : Pl D) {s : AE D}
    (hs : s ∈ idAt D (· = v)) (h : ∀ o ∈ intAt D (· = v), psiE ψ (s * o) = 1) : s ∈ idV (dI D) v := by
  have hs1 : infPart D s = 0 := hs.1
  have hinf : ∀ o, infPart D (s * o) = 0 := fun o => by
    rw [RingHom.map_mul, hs1, zero_mul]
  have hz : (singleV D.host.F v 1 ⊗ₜ[D.host.F] (1 : D.host.E)) * finPart D s = finPart D s :=
    Conductor.idem_mul v _ fun w hw => (Submodule.mem_iInf _).1 hs.2 ⟨w, hw⟩
  obtain ⟨x, u, hu, e⟩ := Conductor.approx (finPart D s)
  have hε : singleV D.host.F v 1 ∈ intAf D.host.F := by
    have := Conductor.idem_mul_mem (v := v) (α := 1) (by rw [map_one]; exact one_mem _)
    rwa [mul_one] at this
  have hx : TrInt D x := fun o => by
    have h1 := h _ (Conductor.lift_mem v o)
    have e1 : singleV D.host.F v 1 ⊗ₜ[D.host.F] (o : D.host.E) =
        (singleV D.host.F v 1 ⊗ₜ[D.host.F] (1 : D.host.E)) * (1 ⊗ₜ[D.host.F] (o : D.host.E)) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rw [Conductor.psiE_eq_chi ψ (hinf _), RingHom.map_mul, GlobalTheory.LatVac.finPart_pair, e1, ← mul_assoc,
      mul_comm (finPart D s), hz, e, add_mul, Conductor.chi_add,
      Conductor.chi_int hψ (Conductor.mul_mem_int hu (Conductor.tmul_mem (GlobalTheory.LatVac.one_mem_intAf _) o)), mul_one,
      Algebra.TensorProduct.tmul_mul_tmul, mul_one] at h1
    exact (Conductor.chi_rat hψ _).1 h1
  have hfin : finPart D s = singleV D.host.F v 1 ⊗ₜ[D.host.F] x +
      (singleV D.host.F v 1 ⊗ₜ[D.host.F] (1 : D.host.E)) * u := by
    rw [← hz, e, mul_add, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  rw [eq_lift hs1, hfin, map_add (f := _)]
  exact add_mem (AddSubgroup.subset_closure ⟨_, hε, fun w hw => Conductor.ev_ne hw, x, (mem_dI_iff x).2 hx,
    lift_tmul _ _⟩) (lift_int_mem v hε hu)

theorem idV_dI_iff : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (v : Pl D),
    ∀ s ∈ idAt D (· = v), s ∈ idV (dI D) v ↔ ∀ o ∈ intAt D (· = v), psiE ψ (s * o) = 1 :=
  fun _ _ hψ v _ hs => ⟨fun h => forward hψ v h, backward hψ v hs⟩

end GlobalTheory.SeeSaw.DiffDual

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.LocMod GlobalTheory.StepData

theorem _root_.GlobalTheory.T.fourierJacobi_bessel_flatMap_factor_isLocalModel : ∀ (D : D7), GlobalTheory.FinPl.FlatLaws D → OmLoc D → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (p : Place D k) (ν : Measure k), ν.IsAddHaarMeasure → ∀ (ψ : AddChar (AF D.host.F) ℂ) (ψk : AddChar k Circle), p.IsChar ψ ψk → ∀ (σ : ℕ) (J : JacLev D (σ + 1)) (B : BesLev D σ) (st : StepFB ψ J B) (s : k), s ≠ 0 → ∀ (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c : ℕ) (G₀ : Frame k J.W₀.rank n') (FW : Frame k J.W.rank (n' ⊕ Fin (c + 1))) (FA : Frame k B.A.rank n) (F₀ : Frame k B.V₀.rank (n ⊕ Unit)) (FV : Frame k B.V.rank (n ⊕ Fin c)), p.IsJacFrame J s (-p.xi ^ 2 * p.hz B) G₀ FW → p.IsCoreFrame B (s * p.xi) FA F₀ → p.IsBesFrame B (s * p.xi) FA FV → ∀ Tm, p.IsModel ψ FW FV Tm → ∀ (T₀ : SB (Matrix (n ⊕ Unit) n' k) →ₗ[ℂ] (WO J.W₀ B.V₀ → ℂ)), (∀ (Φ : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)) (Ψ : SB (Matrix (n ⊕ Unit) n' k)), Ψ.1 = GlobalTheory.LocFlat.flRow ψk ν (σ + 1) Φ.1 → flatFB st (Tm Φ) = T₀ Ψ) → p.IsModel ψ G₀ F₀ T₀ := by
  first | exact @GlobalTheory.LocFlatFB.factor_isModel | exact GlobalTheory.LocFlatFB.factor_isModel | (intros; apply GlobalTheory.LocFlatFB.factor_isModel <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.LocMod GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain ValuativeRel

namespace GlobalTheory.SeeSaw.LocTarget

theorem isLoc_one {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : Place D k) {Y : Type} [Fintype Y] [DecidableEq Y] {S : HSp D} (F : GlobalTheory.LocMod.Frame k S.rank Y) : p.IsLoc F 1 1 := by
  have h1 : Formalism.L2.Theta.mt S 1 = 1 := by simp [Formalism.L2.Theta.mt]
  refine ⟨fun i j => by rw [h1, sub_self, Matrix.zero_apply, mul_zero], ?_⟩
  rw [h1, Units.val_one, Matrix.mul_one, F.βγ]
  exact Matrix.map_one _ (map_zero _) (map_one _)

theorem isComp_inv {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : Place D k) {χ : (AE D)ˣ →* Circle} {μ : kˣ →* ℂˣ} (h : p.IsComp χ⁻¹ μ) : p.IsComp χ μ⁻¹ := by
  intro x a ha
  rw [MonoidHom.inv_apply, Units.val_inv_eq_inv_val, h x a ha, MonoidHom.inv_apply, Circle.coe_inv, inv_inv]

theorem om_phi {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {s κ : ℕ}
    (S : SymData k s κ) (t : Type) [Fintype t] [DecidableEq t] (μ : ℕ → kˣ →* ℂˣ) (hμ : ∀ j, IsTame (μ j))
    (hu : ∀ j (x : kˣ), valuation k (x : k) = 1 → μ j x = S.μ j x) (j b : ℕ) (H : j + b = s) (hb : j + 1 + b = s + 1)
    (x : ((S.T t).lev (j + 1) b hb).J) :
    GlobalTheory.SplitWeil.om (μ (j + 1)) 1 x.1 ((S.T t).Phi j b H) =
      ((((S.T t).lev (j + 1) b hb).lam x : ℂ))⁻¹ • (S.T t).Phi j b H := by
  obtain ⟨h1, h2⟩ := GlobalTheory.SeeSaw.MuUnits.withMu_eq k s κ S t μ hμ hu
  have hL : ((withMu S μ hμ).T t).Laws := Chain.ofType_laws _ _ _ _ _
  obtain ⟨hJ, hl⟩ := h2 (j + 1) b hb
  have hx : x.1 ∈ (((withMu S μ hμ).T t).lev (j + 1) b hb).J := by rw [hJ]; exact x.2
  have := (hL.1 j b H).2 ⟨x.1, hx⟩
  rw [h1, hl x.1 hx x.2, Units.val_inv_eq_inv_val] at this
  exact this

end GlobalTheory.SeeSaw.LocTarget
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.RootEx GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.SplitWeil GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.fourierJacobiNormalFrame_isotropicColumns_pairing : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k) (ρ : ℕ) (J : JacLev D ρ) (n : Type) [Fintype n] [DecidableEq n] (c : ℕ) (s hh : k) (F₀ : Frame k J.W₀.rank n) (F : Frame k J.W.rank (n ⊕ Fin c)), p.IsJacFrame J s hh F₀ F → ∀ i : Fin ρ, ∃ m₀ m₁ : n ⊕ Fin c, (∀ r, F.β r m₀ = s * p.xi ^ (ρ - i.val) * p.pr (J.d.e r i)) ∧ (∀ r, F.β r m₁ = s * (hh / p.xi) * (-1 / p.xi) ^ (ρ - 1 - i.val) * p.pr (J.d.e' r i)) ∧ ∀ m, m ≠ m₁ → ∑ r, ∑ r', p.pr (star (J.d.e r i)) * p.pr (J.W.gram r r') * F.β r' m = 0 := by
  first | exact @GlobalTheory.LocMod.JacCols.cols_pair | exact GlobalTheory.LocMod.JacCols.cols_pair | (intros; apply GlobalTheory.LocMod.JacCols.cols_pair <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_continuous_local_GL_embedding_splitPlace : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k) (V : HSp D) (Y : Type) [Fintype Y] [DecidableEq Y] (F : GlobalTheory.LocMod.Frame k V.rank Y), ∃ gl : GL Y k →* GA D V, Continuous gl ∧ (∀ x, SuppAt q.e V (gl x) ∧ (mt V (gl x)).map q.pr = F.β * x.val * F.γ) ∧ ∀ g x, SuppAt q.e V g → (mt V g).map q.pr = F.β * x.val * F.γ → g = gl x := by
  first | exact @GlobalTheory.LocEmb.exists_gl | exact GlobalTheory.LocEmb.exists_gl | (intros; apply GlobalTheory.LocEmb.exists_gl <;> assumption)
end
