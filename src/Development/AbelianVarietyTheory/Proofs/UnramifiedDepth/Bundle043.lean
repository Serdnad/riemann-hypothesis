module

public import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.IsEigBasisIff
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle033
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle002
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle039
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle036
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle037
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.TwoMulChainStartIndexAddOneOfOdd
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle034
import Formalism.LocalToGlobal.CharacterGerms.Bundle006
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ChF

private theorem finrank_iSup_indep {K V I : Type} [Field K] [AddCommGroup V] [Module K V] [Module.Finite K V]
    [Fintype I] (S : I → Submodule K V) (hi : iSupIndep S) :
    Module.finrank K ↥(⨆ i, S i) = ∑ i, Module.finrank K (S i) := by
  classical
  rw [Submodule.iSup_eq_range_dfinsupp_lsum, LinearMap.finrank_range_of_inj hi.dfinsupp_lsum_injective]
  exact Module.finrank_directSum (R := K) (fun i => S i)

private theorem range_idem {O : Type} [CommRing O] [IsLocalRing O] {g : ℕ} (P : Matrix (Fin g) (Fin g) O)
    (h : P * P = P) : ∃ r : ℕ, Matrix.trace P = (r : O) ∧ Module.finrank O (LinearMap.range (Matrix.mulVecLin P)) = r ∧
      Nonempty (LinearMap.range (Matrix.mulVecLin P) ≃ₗ[O] (Fin r → O)) := by
  have hf : IsIdempotentElem (Matrix.mulVecLin P) := by
    show Matrix.mulVecLin P ∘ₗ Matrix.mulVecLin P = _
    rw [← Matrix.mulVecLin_mul, h]
  have hp := LinearMap.IsIdempotentElem.isProj_range _ hf
  haveI : Module.Projective O (LinearMap.range (Matrix.mulVecLin P)) :=
    Module.Projective.of_split (LinearMap.range (Matrix.mulVecLin P)).subtype hp.codRestrict (by
      ext x : 1
      exact hp.codRestrict_apply_cod x)
  haveI : Module.Free O (LinearMap.range (Matrix.mulVecLin P)) := Module.free_of_flat_of_isLocalRing
  haveI : Module.Projective O (LinearMap.ker (Matrix.mulVecLin P)) := by
    have hq := LinearMap.IsIdempotentElem.isProj_range _ hf.one_sub
    have : LinearMap.range (1 - Matrix.mulVecLin P) = LinearMap.ker (Matrix.mulVecLin P) :=
      (LinearMap.IsIdempotentElem.ker_eq_range_one_sub hf).symm
    rw [this] at hq
    exact Module.Projective.of_split (LinearMap.ker (Matrix.mulVecLin P)).subtype hq.codRestrict (by
      ext x : 1
      exact hq.codRestrict_apply_cod x)
  haveI : Module.Finite O (LinearMap.ker (Matrix.mulVecLin P)) := by
    rw [LinearMap.IsIdempotentElem.ker_eq_range_one_sub hf]
    infer_instance
  haveI : Module.Free O (LinearMap.ker (Matrix.mulVecLin P)) := Module.free_of_flat_of_isLocalRing
  refine ⟨_, ?_, rfl, ⟨(Module.finBasis O _).equivFun⟩⟩
  rw [← hp.trace, ← Matrix.toLin'_apply', Matrix.trace_toLin'_eq]

theorem range_idempotent_equiv_sum_eigDim : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C], v.Integers O → ∀ [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [Algebra ℤ_[p] O] (OE : Type) [CommRing OE] [IsDedekindDomain OE] [CharZero OE] [Module.Free ℤ OE] [Module.Finite ℤ OE] [StarRing OE] (g : ℕ) (ρ : (ℤ_[p] ⊗[ℤ] OE) →+* Matrix (Fin g) (Fin g) O) (e : ℤ_[p] ⊗[ℤ] OE), e * e = e → ∀ (n : ℕ) (t : Fin n ≃ Emb (O := O) e), Nonempty (LinearMap.range (Matrix.mulVecLin (ρ e)) ≃ₗ[O] (Fin (∑ j, eigDim C (fun a : OE => ρ (1 ⊗ₜ[ℤ] a)) ((algebraMap O C).comp ((t j : Emb (O := O) e) : OE →+* O))) → O)) := by
  intro p _ C _ _ _ v O _ _ hv _ _ _ OE _ _ _ _ _ _ g ρ e he n t
  haveI : IsDomain O := hv.hom_inj.isDomain (algebraMap O C)
  haveI : ValuationRing O := ValuationRing.of_integers v hv
  have hP : ρ e * ρ e = ρ e := by rw [← map_mul, he]
  obtain ⟨r, htr, -, hne⟩ := range_idem (ρ e) hP
  have hPC : (ρ e).map (algebraMap O C) * (ρ e).map (algebraMap O C) = (ρ e).map (algebraMap O C) := by
    rw [← Matrix.map_mul, hP]
  obtain ⟨r', htr', hrk, -⟩ := range_idem _ hPC
  have hrr : r = r' := by
    have : ((r : ℕ) : C) = r' := by
      rw [← htr', ← AddMonoidHom.map_trace (algebraMap O C) (ρ e), htr]
      simp
    exact_mod_cast this
  let σ : (ℤ_[p] ⊗[ℤ] OE) →+* Module.End C (Fin g → C) :=
    (Matrix.toLinAlgEquiv' (R := C) (n := Fin g)).toRingEquiv.toRingHom.comp
      ((algebraMap O C).mapMatrix.comp ρ)
  have hσ : ∀ x, σ x = Matrix.toLin' ((ρ x).map (algebraMap O C)) := fun x => rfl
  let ρE : OE →+* Module.End C (Fin g → C) :=
    σ.comp (Algebra.TensorProduct.includeRight (R := ℤ) (A := ℤ_[p]) (B := OE)).toRingHom
  obtain ⟨-, hd⟩ := GlobalTheory.order_rep_diagonalisable C OE
  obtain ⟨hind, htop⟩ := hd (Fin g → C) ρE
  obtain ⟨hex, h01, -⟩ := GlobalTheory.ChF.embeddings_idempotents_conjugation p C v O hv OE
  have hz := (GlobalTheory.ChF.padicInt_algebra_of_isAdicComplete_and_matrix_unique p O).2 g
    (ρ.comp (Algebra.TensorProduct.includeLeftRingHom (R := ℤ) (A := ℤ_[p]) (B := OE)))
  set E : (OE →+* C) → Submodule C (Fin g → C) :=
    fun τ => ⨅ a : OE, Module.End.eigenspace (ρE a) (τ a) with hE
  have hact : ∀ (τ : OE →+* O) (y : Fin g → C), y ∈ E ((algebraMap O C).comp τ) →
      ∀ x, σ x y = algebraMap O C (tauExt τ x) • y := by
    intro τ y hy x
    have hy' : ∀ a, σ (1 ⊗ₜ[ℤ] a) y = algebraMap O C (τ a) • y := by
      intro a
      have := (Submodule.mem_iInf _).1 hy a
      exact Module.End.mem_eigenspace_iff.1 this
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x x' h h' => rw [map_add (f := _), map_add (f := _), map_add (f := _), LinearMap.add_apply, h, h', add_smul]
    | tmul c a =>
      have h1 : (c ⊗ₜ[ℤ] a : ℤ_[p] ⊗[ℤ] OE) = (c ⊗ₜ[ℤ] 1) * (1 ⊗ₜ[ℤ] a) := by simp
      have h2 : ρ (c ⊗ₜ[ℤ] 1) = algebraMap ℤ_[p] O c • (1 : Matrix (Fin g) (Fin g) O) := hz c
      have h3 : ∀ z, σ (c ⊗ₜ[ℤ] 1) z = algebraMap O C (algebraMap ℤ_[p] O c) • z := by
        intro z
        have : (algebraMap ℤ_[p] O c • (1 : Matrix (Fin g) (Fin g) O)).map (algebraMap O C)
            = algebraMap O C (algebraMap ℤ_[p] O c) • (1 : Matrix (Fin g) (Fin g) C) := by
          ext i j
          rw [Matrix.map_apply, Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul, map_mul,
            Matrix.one_apply, Matrix.one_apply]
          split_ifs
          · rw [map_one]
          · rw [map_zero]
        rw [hσ, h2, this, map_smul, Matrix.toLin'_one]
        rfl
      have h4 : tauExt τ (c ⊗ₜ[ℤ] a) = algebraMap ℤ_[p] O c * τ a := by
        simp [tauExt, Algebra.ofId_apply]
      rw [h4, h1, map_mul, Module.End.mul_apply, h3, hy', smul_smul, map_mul]
  have hinj : Function.Injective
      (fun j : Fin n => (algebraMap O C).comp ((t j : Emb (O := O) e) : OE →+* O)) := by
    intro i j hij
    apply t.injective
    apply Subtype.ext
    exact (hex _).unique hij rfl
  have hrange : LinearMap.range (σ e) =
      ⨆ j : Fin n, E ((algebraMap O C).comp ((t j : Emb (O := O) e) : OE →+* O)) := by
    apply le_antisymm
    · rw [LinearMap.range_eq_map, ← htop, Submodule.map_iSup]
      refine iSup_le fun τ => ?_
      rintro _ ⟨y, hy, rfl⟩
      obtain ⟨τ', rfl, -⟩ := hex τ
      rw [hact τ' y hy e]
      rcases h01 e τ' he with h | h
      · rw [h]; simp
      · rw [h, map_one, one_smul]
        refine Submodule.mem_iSup_of_mem (t.symm ⟨τ', h⟩) ?_
        rw [Equiv.apply_symm_apply]
        exact hy
    · refine iSup_le fun j => fun y hy => ⟨y, ?_⟩
      have h : tauExt ((t j : Emb (O := O) e) : OE →+* O) e = 1 := (t j).2
      rw [hact _ y hy e, h, map_one, one_smul]
  have hsum := finrank_iSup_indep _ (hind.comp hinj)
  have hfin : r' = ∑ j, eigDim C (fun a : OE => ρ (1 ⊗ₜ[ℤ] a))
      ((algebraMap O C).comp ((t j : Emb (O := O) e) : OE →+* O)) := by
    have h1 : Module.finrank C (LinearMap.range (σ e)) = r' := hrk
    rw [← h1, hrange]
    exact hsum
  rw [← hfin, ← hrr]
  exact hne

end GlobalTheory.ChF
end

section

set_option autoImplicit false
noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ChF

private theorem hs {R : Type} [CommRing R] {m n d e : ℕ} (a : Fin m → Fin d → PS R n e)
    (h : ∀ i j, MvPowerSeries.constantCoeff (a i j) = 0) :
    MvPowerSeries.HasSubst (fun q : Fin m × Fin d => a q.1 q.2) :=
  MvPowerSeries.hasSubst_of_constantCoeff_zero (fun q => h q.1 q.2)

private theorem sub_sub' {R : Type} [CommRing R] {m n k d e f : ℕ} (a : Fin m → Fin d → PS R n e)
    (b : Fin n → Fin e → PS R k f) (ha : ∀ i j, MvPowerSeries.constantCoeff (a i j) = 0)
    (hb : ∀ i j, MvPowerSeries.constantCoeff (b i j) = 0) (u : PS R m d) :
    sub b (sub a u) = sub (fun i j => sub b (a i j)) u :=
  MvPowerSeries.subst_comp_subst_apply (hs a ha) (hs b hb) u

private theorem sub_X {R : Type} [CommRing R] {m n d e : ℕ} (a : Fin m → Fin d → PS R n e)
    (ha : ∀ i j, MvPowerSeries.constantCoeff (a i j) = 0) (q : Fin m × Fin d) :
    sub a (MvPowerSeries.X q) = a q.1 q.2 :=
  MvPowerSeries.subst_X (hs a ha) q

private theorem sub_mul' {R : Type} [CommRing R] {m n d e : ℕ} (a : Fin m → Fin d → PS R n e)
    (ha : ∀ i j, MvPowerSeries.constantCoeff (a i j) = 0) (u v : PS R m d) :
    sub a (u * v) = sub a u * sub a v :=
  MvPowerSeries.subst_mul (hs a ha) u v

private theorem const_sub {R : Type} [CommRing R] {m n d e : ℕ} (a : Fin m → Fin d → PS R n e)
    (ha : ∀ i j, MvPowerSeries.constantCoeff (a i j) = 0) (u : PS R m d) :
    MvPowerSeries.constantCoeff (sub a u) = MvPowerSeries.constantCoeff u := by
  obtain ⟨-, -, h3, -, -, h6⟩ := nv_calculus R R (RingHom.id R) n e 0 (fun _ _ => IsNilpotent.zero)
  obtain ⟨-, -, -, -, -, h6'⟩ := nv_calculus R R (RingHom.id R) m d 0 (fun _ _ => IsNilpotent.zero)
  have h6 := h6 (by simp)
  have h6' := h6' (by simp)
  have h := h3 m d a u ha
  have e0 : (fun i j => nv (RingHom.id R) (a i j) 0) = 0 := by
    funext i j
    rw [h6, ha]; simp
  rw [e0, h6, h6'] at h
  simpa using h

private theorem coeff_sub {R : Type} [CommRing R] {d e : ℕ} (φ : Fin e → PS R 1 d)
    (hφ : ∀ j, MvPowerSeries.constantCoeff (φ j) = 0) (u : PS R 1 e) (k : Fin d) :
    dl (sub ![φ] u) k = ∑ i, lin φ i k * dl u i := by
  classical
  have hφ' : ∀ (i : Fin 1) j, MvPowerSeries.constantCoeff ((![φ] : Fin 1 → _) i j) = 0 := by
    intro i j; fin_cases i; exact hφ j
  let s : R →+* TrivSqZeroExt R R := algebraMap R _
  let a : Fin 1 → Fin d → TrivSqZeroExt R R := fun _ j => TrivSqZeroExt.inr (if j = k then 1 else 0)
  let b : Fin 1 → Fin e → TrivSqZeroExt R R := fun _ j => TrivSqZeroExt.inr (lin φ j k)
  have hn : ∀ x : R, IsNilpotent (TrivSqZeroExt.inr x : TrivSqZeroExt R R) := fun x =>
    ⟨2, by rw [pow_two, TrivSqZeroExt.inr_mul_inr]⟩
  obtain ⟨-, -, h3, -, -, h6⟩ := nv_calculus R _ s 1 d a (fun _ _ => hn _)
  obtain ⟨-, -, -, -, -, h6'⟩ := nv_calculus R _ s 1 e b (fun _ _ => hn _)
  have h6 := h6 (fun _ _ _ _ => TrivSqZeroExt.inr_mul_inr _ _ _)
  have h6' := h6' (fun _ _ _ _ => TrivSqZeroExt.inr_mul_inr _ _ _)
  have h := h3 1 e ![φ] u hφ'
  have e0 : (fun i j => nv s ((![φ] : Fin 1 → _) i j) a) = b := by
    funext i j
    fin_cases i
    rw [h6, hφ']
    ext
    · have hf : ∀ (t : Finset (Fin 1 × Fin d)) (g : Fin 1 × Fin d → TrivSqZeroExt R R),
          (∑ q ∈ t, g q).fst = ∑ q ∈ t, (g q).fst := fun t g =>
        map_sum (TrivSqZeroExt.fstHom R R R) g t
      simp [s, a, b, hf, apply_ite TrivSqZeroExt.fst]
    · simp [s, a, b, TrivSqZeroExt.snd_sum, Fintype.sum_prod_type, lin, TrivSqZeroExt.algebraMap_eq_inl]
  rw [e0, h6, h6'] at h
  have h2 := congrArg TrivSqZeroExt.snd h
  simpa [s, a, b, TrivSqZeroExt.snd_sum, Fintype.sum_prod_type, TrivSqZeroExt.algebraMap_eq_inl, dl,
    mul_comm] using h2

theorem chain_rule_lin : ∀ (R : Type) [CommRing R] (d e : ℕ) (φ : Fin e → PS R 1 d), (∀ j, MvPowerSeries.constantCoeff (φ j) = 0) → (∀ u : PS R 1 e, dl (sub ![φ] u) = (lin φ)ᵀ *ᵥ dl u ∧ MvPowerSeries.constantCoeff (sub ![φ] u) = MvPowerSeries.constantCoeff u) ∧ (∀ (m : ℕ) (ψ : Fin m → PS R 1 e), lin (fun j => sub ![φ] (ψ j)) = lin ψ * lin φ) ∧ ∀ (F : FGLaw R d) (F' : FGLaw R e), IsHomF F.F F'.F φ → ∀ u, IsCh F'.F u → IsCh F.F (sub ![φ] u) := by
  intro R _ d e φ hφ
  have one : ∀ {n f g : ℕ} (x : Fin g → PS R n f), (∀ j, MvPowerSeries.constantCoeff (x j) = 0) →
      ∀ (i : Fin 1) j, MvPowerSeries.constantCoeff ((![x] : Fin 1 → _) i j) = 0 := by
    intro n f g x hx i j; fin_cases i; exact hx j
  have two : ∀ {n f g : ℕ} (x y : Fin g → PS R n f), (∀ j, MvPowerSeries.constantCoeff (x j) = 0) →
      (∀ j, MvPowerSeries.constantCoeff (y j) = 0) →
      ∀ (i : Fin 2) j, MvPowerSeries.constantCoeff ((![x, y] : Fin 2 → _) i j) = 0 := by
    intro n f g x y hx hy i j; fin_cases i
    · exact hx j
    · exact hy j
  have hφ' := one φ hφ
  refine ⟨fun u => ⟨?_, const_sub _ hφ' u⟩, fun m ψ => ?_, fun F F' hF u hu => ⟨?_, ?_⟩⟩
  · funext k
    rw [coeff_sub φ hφ u k]
    rfl
  · ext j k
    have := coeff_sub φ hφ (ψ j) k
    rw [Matrix.mul_apply]
    refine this.trans (Finset.sum_congr rfl fun i _ => mul_comm _ _)
  · rw [const_sub _ hφ' u, hu.1]
  · have hpt : ∀ (f : ℕ) (i : Fin 2) j, MvPowerSeries.constantCoeff (pt R (n := 2) f i j) = 0 :=
      fun f i j => MvPowerSeries.constantCoeff_X _
    have hid : ∀ (f : ℕ) (G : Fin f → PS R 2 f), addOf G (pt R (n := 2) f 0) (pt R (n := 2) f 1) = G := by
      intro f G
      funext i
      have : (fun p : Fin 2 × Fin f => (![pt R (n := 2) f 0, pt R (n := 2) f 1] : Fin 2 → _) p.1 p.2)
          = MvPowerSeries.X := by
        funext ⟨p, q⟩
        fin_cases p <;> rfl
      simp only [addOf, ev]
      rw [this, MvPowerSeries.subst_self]
      rfl
    have hu2 := hu.2
    rw [hid] at hu2 ⊢
    set x : Fin e → PS R 2 d := fun i => sub ![pt R (n := 2) d 0] (φ i) with hx
    set y : Fin e → PS R 2 d := fun i => sub ![pt R (n := 2) d 1] (φ i) with hy
    have hx0 : ∀ j, MvPowerSeries.constantCoeff (x j) = 0 := fun j => by
      rw [hx]; dsimp only; rw [const_sub _ (one _ (hpt d 0)), hφ]
    have hy0 : ∀ j, MvPowerSeries.constantCoeff (y j) = 0 := fun j => by
      rw [hy]; dsimp only; rw [const_sub _ (one _ (hpt d 1)), hφ]
    have hxy := two x y hx0 hy0
    have h : sub ![x, y] (sub ![F'.F] u) =
        sub ![x, y] (sub ![pt R (n := 2) e 0] u * sub ![pt R (n := 2) e 1] u) := congrArg _ hu2
    rw [sub_mul' _ hxy, sub_sub' _ _ (one _ F'.const) hxy, sub_sub' _ _ (one _ (hpt e 0)) hxy,
      sub_sub' _ _ (one _ (hpt e 1)) hxy] at h
    change sub ![F.F] (sub ![φ] u) =
      sub ![pt R (n := 2) d 0] (sub ![φ] u) * sub ![pt R (n := 2) d 1] (sub ![φ] u)
    rw [sub_sub' _ _ hφ' (one _ F.const), sub_sub' _ _ hφ' (one _ (hpt d 0)),
      sub_sub' _ _ hφ' (one _ (hpt d 1))]
    have e1 : (fun i j => sub ![F.F] ((![φ] : Fin 1 → _) i j)) =
        fun i j => sub ![x, y] ((![F'.F] : Fin 1 → _) i j) := by
      funext i j; fin_cases i; exact hF.2 j
    have e2 : (fun i j => sub ![pt R (n := 2) d 0] ((![φ] : Fin 1 → _) i j)) =
        fun i j => sub ![x, y] ((![pt R (n := 2) e 0] : Fin 1 → _) i j) := by
      funext i j; fin_cases i; exact (sub_X _ hxy (0, j)).symm
    have e3 : (fun i j => sub ![pt R (n := 2) d 1] ((![φ] : Fin 1 → _) i j)) =
        fun i j => sub ![x, y] ((![pt R (n := 2) e 1] : Fin 1 → _) i j) := by
      funext i j; fin_cases i; exact (sub_X _ hxy (1, j)).symm
    rw [e1, e2, e3]
    exact h

end GlobalTheory.ChF
end
end

section

set_option autoImplicit false
noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ChF

private def tv {R S : Type} [CommRing R] [CommRing S] [Algebra R S] (e : S) {n : ℕ} (v : Fin n → R) :
    Fin n → S := fun i => algebraMap R S (v i) * e

private theorem tv_nil {R S : Type} [CommRing R] [CommRing S] [Algebra R S] {e : S} (he : e * e = 0) {n : ℕ}
    (v : Fin n → R) (i : Fin n) : IsNilpotent (tv e v i) :=
  ⟨2, by simp only [tv, mul_pow, pow_two e, he, mul_zero]⟩

private theorem nv_tv {R S : Type} [CommRing R] [CommRing S] [Algebra R S] {e : S} (he : e * e = 0) {n m : ℕ}
    (φ : Fin m → PS R 1 n) (hφ : ∀ j, MvPowerSeries.constantCoeff (φ j) = 0) (v : Fin n → R) :
    (fun j => nv (algebraMap R S) (φ j) ![tv e v]) = tv e (lin φ *ᵥ v) := by
  funext j
  have h := (nv_calculus R S (algebraMap R S) 1 n ![tv e v] (fun i k => by
    fin_cases i; exact tv_nil he v k)).2.2.2.2.2 (fun i k i' k' => by
      fin_cases i; fin_cases i'
      show algebraMap R S (v k) * e * (algebraMap R S (v k') * e) = 0
      rw [_root_.mul_mul_mul_comm, he, mul_zero]) (φ j)
  rw [h, hφ, map_zero, zero_add, Fintype.sum_prod_type, Fin.sum_univ_one]

  simp only [tv, lin, Matrix.mulVec, dotProduct, Matrix.of_apply, map_sum, map_mul, Finset.sum_mul,
  Matrix.cons_val_fin_one, _root_.mul_assoc]

private theorem mat_ext {R : Type} [CommRing R] (I : Ideal R) [IsAdicComplete I R] {m n : ℕ}
    (A A' : Matrix (Fin m) (Fin n) R)
    (h : ∀ (S : Type) [CommRing S] [Algebra R S], (∃ k, Kills I k S) → ∀ e : S, e * e = 0 →
      ∀ v : Fin n → R, tv e (A *ᵥ v) = tv e (A' *ᵥ v)) : A = A' := by
  ext i j
  rw [← sub_eq_zero]
  refine IsHausdorff.haus (IsAdicComplete.toIsHausdorff (I := I) (M := R)) _ fun k => ?_
  have hk : Kills I k (DualNumber (R ⧸ I ^ (k + 1))) := fun t ht => by
    rw [IsScalarTower.algebraMap_apply R (R ⧸ I ^ (k + 1)), Ideal.Quotient.algebraMap_eq,
      Ideal.Quotient.eq_zero_iff_mem.2 ht, map_zero]
  have h1 := congrArg TrivSqZeroExt.snd (congrFun (h (DualNumber (R ⧸ I ^ (k + 1))) ⟨k, hk⟩ DualNumber.eps
    DualNumber.eps_mul_eps (Pi.single j 1)) i)
  simp only [tv, Matrix.mulVec_single_one, Matrix.col_apply,
    IsScalarTower.algebraMap_apply R (R ⧸ I ^ (k + 1)) (DualNumber (R ⧸ I ^ (k + 1))),
    ← Algebra.smul_def, TrivSqZeroExt.snd_smul, DualNumber.snd_eps, smul_eq_mul, _root_.mul_one,
    Ideal.Quotient.algebraMap_eq] at h1
  rw [SModEq.zero, smul_eq_mul, Ideal.mul_top]
  exact Ideal.pow_le_pow_right (Nat.le_succ k) (Ideal.Quotient.eq.1 h1)

private def chi {R S X : Type} [CommRing R] [CommRing S] [Algebra R S] [AddCommGroup X] {e : S}
    (he : e * e = 0) (L : X →+ R) : Multiplicative X →* Sˣ :=
  MonoidHom.toHomUnits
    { toFun := fun y => 1 + algebraMap R S (L y.toAdd) * e
      map_one' := by simp
      map_mul' := fun y z => by
        simp only [toAdd_mul, map_add (f := _)]
        linear_combination (-(algebraMap R S (L y.toAdd) * algebraMap R S (L z.toAdd))) * he }

theorem lin_tangentSeq_equivariant : ∀ (R : Type) [CommRing R] (I : Ideal R) [IsAdicComplete I R] (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (B : Over (Spec (CommRingCat.of R))) [GrpObj B] [IsCommMonObj B] (X : Type) [AddCommGroup X] (E : PtExt I G B X) (d g : ℕ) (F : FGLaw R d) (FB : FGLaw R g) (x : Fam G d) (xB : Fam B g), NilChart G F.F x → NilChart B FB.F xB → ∀ (r : ℕ) (β : Module.Basis (Fin r) ℤ X) (J : Fin d → PS R 1 r) (Q : Fin g → PS R 1 d), (∀ j, MvPowerSeries.constantCoeff (J j) = 0) → (∀ j, MvPowerSeries.constantCoeff (Q j) = 0) → (∀ (S : Type) [CommRing S] [Algebra R S] (h : ∃ k, Kills I k S) (a : Fin d → S), (∀ i, IsNilpotent (a i)) → E.q S h (x S a) = xB S (fun j => nv (algebraMap R S) (Q j) ![a])) → (∀ (S : Type) [CommRing S] [Algebra R S] (h : ∃ k, Kills I k S) (χ : Multiplicative X →* Sˣ) (t : Fin r → S), (∀ i, IsNilpotent (t i)) → (∀ j, (χ (Multiplicative.ofAdd (β j)) : S) = 1 + t j) → E.i S h χ = x S (fun j => nv (algebraMap R S) (J j) ![t])) → ∀ (f : G ⟶ G) (α : Fin d → PS R 1 d), Reads x x f α → (∀ (fB : B ⟶ B) (αB : Fin g → PS R 1 g), Reads xB xB fB αB → (∀ (S : Type) [CommRing S] [Algebra R S] (h : ∃ k, Kills I k S) z, E.q S h (z ≫ f) = E.q S h z ≫ fB) → lin Q * lin α = lin αB * lin Q) ∧ ∀ hm : X →+ X, (∀ (S : Type) [CommRing S] [Algebra R S] (h : ∃ k, Kills I k S) χ χ', (∀ y, χ' (Multiplicative.ofAdd y) = χ (Multiplicative.ofAdd (hm y))) → E.i S h χ ≫ f = E.i S h χ') → lin α * lin J = lin J * Matrix.of (fun i k => ((β.repr (hm (β i)) k : ℤ) : R)) := by
  intro R _ I _ G _ _ B _ _ X _ E d g F FB x xB hx hxB r β J Q hJ hQ hq hi f α hα
  refine ⟨fun fB αB hαB hc => mat_ext I _ _ fun S _ _ h e he v => ?_,
    fun hm hc => mat_ext I _ _ fun S _ _ h e he v => ?_⟩
  · refine hxB.inj S _ _ (tv_nil he _) (tv_nil he _) ?_
    have h1 := hc S h (x S (tv e v))
    rw [hα.2 S _ (tv_nil he v), nv_tv he α hα.1, hq S h _ (tv_nil he _), hq S h _ (tv_nil he _),
      nv_tv he Q hQ, nv_tv he Q hQ, hαB.2 S _ (tv_nil he _), nv_tv he αB hαB.1] at h1
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    exact h1
  · refine hx.inj S _ _ (tv_nil he _) (tv_nil he _) ?_
    let L : X →ₗ[ℤ] R := β.constr ℤ v
    have hL : ∀ j, L (β j) = v j := fun j => β.constr_basis ℤ v j
    have hL' : ∀ j, L (hm (β j)) =
        (Matrix.of (fun i k => ((β.repr (hm (β i)) k : ℤ) : R)) *ᵥ v) j := fun j => by
      simp [L, Module.Basis.constr_apply_fintype, Matrix.mulVec, dotProduct]
    have h1 := hc S h (chi he L.toAddMonoidHom) (chi he (L.toAddMonoidHom.comp hm)) (fun y => Units.ext rfl)
    rw [hi S h _ (tv e v) (tv_nil he _) (fun j => by
        show 1 + algebraMap R S (L (β j)) * e = _
        rw [hL]; rfl),
      hi S h _ (tv e (Matrix.of (fun i k => ((β.repr (hm (β i)) k : ℤ) : R)) *ᵥ v)) (tv_nil he _) (fun j => by
        show 1 + algebraMap R S (L (hm (β j))) * e = _
        rw [hL']; rfl),
      nv_tv he J hJ, nv_tv he J hJ, hα.2 S _ (tv_nil he _), nv_tv he α hα.1] at h1
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    exact h1

end GlobalTheory.ChF
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_powerSeries_reading_groupHom_nilpotentCharts : ∀ (R : Type) [CommRing R] (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (G' : Over (Spec (CommRingCat.of R))) [GrpObj G'] [IsCommMonObj G'] (d e : ℕ) (F : Fin d → PS R 2 d) (F' : Fin e → PS R 2 e) (X : Fam G d) (X' : Fam G' e), NilChart G F X → NilChart G' F' X' → ∀ f : G ⟶ G', IsMonHom f → ∃ φ : Fin e → PS R 1 d, Reads X X' f φ := by
  first | exact @GlobalTheory.ChF.exists_reads | exact GlobalTheory.ChF.exists_reads | (intros; apply GlobalTheory.ChF.exists_reads <;> assumption)
end

section

open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds GlobalTheory.MainTerm Classical

namespace GlobalTheory.MainTerm

theorem linPull_coord_int_of_degree_lt :
    ∀ (C : Type) [Field C] (V : VF C) (d : ℕ) (I J : Type) [Fintype I] [Fintype J] (G : Cart V d I J) (S : Sys G) (t : I → MvPowerSeries I C), S.IsT t → ∀ (N : ℕ) (e : Fin N → I → C), (∀ j x, V.Ge 0 (e j x)) → ∀ μ : Fin N →₀ ℕ, μ.degree < V.l → ∀ c, V.Ge 0 (MvPowerSeries.coeff μ (linPull e (t c))) := by
  intro C _ V d I J _ _ G S t ht N e he μ hμ c
  have hz : ∀ b j, V.Ge 0 (S.co (Sum.elim (e j) (0 : J → C)) b) := fun b j =>
    S.co_int (fun n => by
      cases n with
      | inl x => exact he j x
      | inr κ => exact VF.Ge.zero 0) b
  obtain ⟨h0, h1, -⟩ := GlobalTheory.T.formalGroupCoordinates_pullback_linear_tangentBasis C V d I J G S t ht (Fin N) e
    (fun b j => S.co (Sum.elim (e j) (0 : J → C)) b)
    (fun c k b => if k = 0 then (if c = b then 1 else 0) else S.co (S.cur c k) b)
    (fun j x => (S.co_spec (Sum.elim (e j) (0 : J → C)) x).symm)
    (fun c b => by simp)
    (fun c k x hk => by
      have hk' : k ≠ 0 := by omega
      simp only [if_neg hk', Sys.al, S.cur_zero_inl]
      exact (S.co_spec (S.cur c k) x).symm)
  have h2 := h1 c μ
  rw [Finset.sum_range_succ', Finset.sum_eq_zero, zero_add] at h2
  · simp only [if_true, pow_zero, pow_one, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq',
      Finset.mem_univ] at h2

    rw [h2, map_sum]
    refine VF.Ge.sum fun j _ => ?_
    rw [MvPowerSeries.coeff_C_mul, MvPowerSeries.coeff_X]
    refine (hz c j).mul_int ?_
    split_ifs
    · exact VF.Ge.one
    · exact VF.Ge.zero 0
  · intro s _
    refine Finset.sum_eq_zero fun b _ => ?_
    rw [MvPowerSeries.coeff_of_lt_order, mul_zero]
    refine lt_of_lt_of_le ?_ (MvPowerSeries.le_order_pow_of_constantCoeff_eq_zero _ (h0 b))
    have : V.l ≤ V.l ^ (s + 1) := Nat.le_self_pow (Nat.succ_ne_zero s) _
    exact_mod_cast lt_of_lt_of_le hμ this

end GlobalTheory.MainTerm
end
