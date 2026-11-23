module

public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle020
public import Development.AbelianVarietyTheory.Definitions.Foundations.ThNSpec
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle009
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.FrobeniusHodgeTateLaws.Bundle002
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UntwistedRepresentationOrdinaryTriangularShape
public import Formalism.LocalRingCardinality.SpanPowerMembership.Bundle003
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.FieldTheory.Galois.Profinite
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Lemma
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
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsEqSubOfMemCob
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle004
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

@[expose] public section

section

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.CyclotomicQExpansion GlobalTheory.KummerEisensteinGalois GlobalTheory.K4 GlobalTheory.LambdaValuationPowers
open scoped Matrix MatrixGroups TensorProduct

namespace UpperTheory.V.Z.Kato.Joint

def fop {E : Type} [Field E] (k l : ℕ) (χ : ℕ → E) : Letter → Module.End E (ℕ → E)
  | Letter.T q =>
    { toFun := GlobalTheory.EisM.To k (χ q) q
      map_add' := fun a b => by funext n; simp only [GlobalTheory.EisM.To, GlobalTheory.EisM.Vo, Pi.add_apply]; split_ifs <;> ring
      map_smul' := fun c a => by
        funext n; simp only [GlobalTheory.EisM.To, GlobalTheory.EisM.Vo, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; split_ifs <;> ring }
  | Letter.U => { toFun := GlobalTheory.EisM.Uo l, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  | Letter.D d => χ d • 1

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} {l : ℕ} [Fact l.Prime]

def th (X : Tower Ω ε) (A : ValuationSubring Ω) (N : ℕ) (j : Ω →+* Qbar l) (n : ℕ) (b : X.Fn l) : ℕ → Qbar l :=
  seqN 1 j (thN X A N l n 1 b)

def Std (A : ValuationSubring Ω) (N w : ℕ) (j : Ω →+* Qbar l) : Prop :=
  (l : Ω) ∈ A.nonunits ∧ l ≠ 2 ∧ ¬ l ∣ N ∧ 5 ≤ N ∧ Odd w ∧ ∀ x ∈ A, ‖j x‖ ≤ 1

def FormP : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (k N : ℕ) (χ : DirichletCharacter ℂ N) (t : ℕ → ℂ) (α : ℂ) (B : ℕ) (cc : ℕ → ℂ)
    (χE : ℕ → Qbar l) (ev : Letter → Qbar l), 1 ≤ k → GlobalTheory.EisM.EigF k N l χ t α B cc → (∀ d : ℕ, d.Coprime N → ι (χE d) = χ d) →
    (∀ q : ℕ, q.Prime → ¬ q ∣ N * l → ι (ev (Letter.T q)) = t q) → ι (ev Letter.U) = α →
    (∀ d : ℕ, d.Coprime N → ev (Letter.D d) = χE d) → ∀ P ∈ admissibleLettersSubalgebra (Qbar l) N l, ∀ a : ℕ → Qbar l,
    GlobalTheory.EisM.MF k (N * l) (GlobalTheory.EisM.ch χ) (fun i => ι (a i)) →
      GlobalTheory.EisM.lam B cc (fun i => ι (FreeAlgebra.lift (Qbar l) (fop k l χE) P a i)) =
        ι (FreeAlgebra.lift (Qbar l) ev P) * GlobalTheory.EisM.lam B cc fun i => ι (a i)

def FinP : Prop := CoefUb →
  ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (k N : ℕ) (B : ℕ) (cc : ℕ → ℂ) (χE : ℕ → Qbar l) (c₀ : Coef l),
    ∀ P ∈ admissibleLettersSubalgebra (Qbar l) N l, ∃ (lam₀ lam : (ℕ → Qbar l) →ₗ[Qbar l] Qbar l) (c : Coef l), c₀.O ≤ c.O ∧ FinSupp lam₀ ∧ FinSupp lam ∧
      (∀ i : ℕ, FixIc c (lam (Pi.single i 1))) ∧ (∀ a, lam₀ a = ι.symm (GlobalTheory.EisM.lam B cc fun i => ι (a i))) ∧
      ∀ a, lam a = lam₀ (FreeAlgebra.lift (Qbar l) (fop k l χE) P a)

def ThLin : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε)
    (A : ValuationSubring Ω) (N w : ℕ) (j : Ω →+* Qbar l), Std A N w j → ∀ n : ℕ,
    ∃ Θ : (Qbar l ⊗[ℤ_[l]] X.Fn l) →ₗ[Qbar l] (ℕ → Qbar l), ∀ b ∈ X.B N l w, ∀ i, Cg n (Θ ((1 : Qbar l) ⊗ₜ[ℤ_[l]] b) i) (th X A N j n b i)

def ThOp : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε)
    (A : ValuationSubring Ω) (N w : ℕ) (j : Ω →+* Qbar l) (χ : ℕ → ℤ_[l]), Std A N w j → ∀ (n : ℕ) (T : Letter) (b : X.Fn l),
    GlobalTheory.KZ.admitted N l T → InChi X N w χ b →
      ∀ i, Cg n (th X A N j n (X.op N l T b) i) (fop (w + 2) l (fun d => ((χ d : ℤ_[l]) : Qbar l)) T (th X A N j n b) i)

def ChiStab : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε)
    (N w : ℕ) (χ : ℕ → ℤ_[l]), l ≠ 2 → ¬ l ∣ N → 5 ≤ N → Odd w → ∀ (T : Letter) (b : X.Fn l),
    GlobalTheory.KZ.admitted N l T → InChi X N w χ b → InChi X N w χ (X.op N l T b)

def ThP : Prop := ThOp → ChiStab →
  ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε)
    (A : ValuationSubring Ω) (N w : ℕ) (j : Ω →+* Qbar l) (χ : ℕ → ℤ_[l]), Std A N w j → ∀ P ∈ admissibleLettersSubalgebra (Qbar l) N l,
    ∃ c : ℕ, ∀ n, c ≤ n → ∀ Θ : (Qbar l ⊗[ℤ_[l]] X.Fn l) →ₗ[Qbar l] (ℕ → Qbar l),
      (∀ b ∈ X.B N l w, ∀ i, Cg n (Θ ((1 : Qbar l) ⊗ₜ[ℤ_[l]] b) i) (th X A N j n b i)) → ∀ b, InChi X N w χ b → ∀ i,
        Cg (n - c) (FreeAlgebra.lift (Qbar l) (fop (w + 2) l fun d => ((χ d : ℤ_[l]) : Qbar l)) P (th X A N j n b) i)
          (Θ (FreeAlgebra.lift (Qbar l) (X.opV N l (Qbar l)) P ((1 : Qbar l) ⊗ₜ[ℤ_[l]] b)) i)

def ChiQuad : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ι : Qbar l ≃+* ℂ) (e : ℕ) (S : Finset Pl)
    (A : ValuationSubring Ω) (W : R2 Ω l) (g : Newform (2 * e + 1)) (χ : G ℚ Ω →* (Qbar l)ˣ), Nf e S A W → KillsMu l χ →
    ¬ l ∣ g.M → g.Att ι (tw W (cycBar ℚ Ω l ^ (-(e : ℤ)) * (dt W)⁻¹ * χ)) →
    ∀ d : ℕ, d.Coprime g.M → g.χ d = 1 ∨ g.χ d = -1

end UpperTheory.V.Z.Kato.Joint

end
end

section

open UpperTheory.V.Z.Kato.Joint Topology Filter

private theorem mem_fixingSubgroup_of_fixes_finite_set (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω]
    (E : IntermediateField K Ω) [FiniteDimensional K E] :
    ∃ T : Finset Ω, ∀ g : Ω ≃ₐ[K] Ω, (∀ x ∈ T, g x = x) → g ∈ E.fixingSubgroup := by
  have h1 : (Subalgebra.toSubmodule E.toSubalgebra).FG :=
    Module.Finite.iff_fg.1 (inferInstanceAs (Module.Finite K E))
  obtain ⟨t, ht⟩ := h1
  refine ⟨t, fun g hg => ?_⟩
  rw [IntermediateField.mem_fixingSubgroup_iff]
  intro x hx
  have hle : Algebra.adjoin K (t : Set Ω) ≤ AlgHom.equalizer (g : Ω →ₐ[K] Ω) (AlgHom.id K Ω) :=
    Algebra.adjoin_le (fun y hy => by
      rw [SetLike.mem_coe, AlgHom.mem_equalizer]
      simpa using hg y hy)
  have hx1 : x ∈ Submodule.span K (t : Set Ω) := by
    rw [ht]
    exact hx
  have hx2 : x ∈ Algebra.adjoin K (t : Set Ω) := Algebra.span_le_adjoin K _ hx1
  have hx3 := hle hx2
  rw [AlgHom.mem_equalizer] at hx3
  simpa using hx3

private theorem uniform_continuity_galois_group (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω] {X : Type} [NormedAddCommGroup X]
    (f : (Ω ≃ₐ[K] Ω) → X) (hf : Continuous f) (δ : ℝ) (hδ : 0 < δ) :
    ∃ E0 : Finset Ω, ∀ s s' : Ω ≃ₐ[K] Ω, (∀ x ∈ E0, s' x = x) → ‖f (s * s') - f s‖ < δ := by
  classical
  have hδ2 : 0 < δ / 2 := half_pos hδ
  have key : ∀ s : Ω ≃ₐ[K] Ω, ∃ E : IntermediateField K Ω, FiniteDimensional K E ∧
      ∀ g ∈ E.fixingSubgroup, ‖f (s * g) - f s‖ < δ / 2 := by
    intro s
    have hc : Continuous fun g : Ω ≃ₐ[K] Ω => ‖f (s * g) - f s‖ :=
      ((hf.comp (continuous_const.mul continuous_id)).sub continuous_const).norm
    have hA : {g : Ω ≃ₐ[K] Ω | ‖f (s * g) - f s‖ < δ / 2} ∈ 𝓝 (1 : Ω ≃ₐ[K] Ω) :=
      IsOpen.mem_nhds (isOpen_lt hc continuous_const) (by simp [hδ2])
    obtain ⟨E, hE, hsub⟩ := (krullTopology_mem_nhds_one_iff K Ω _).1 hA
    exact ⟨E, hE, fun g hg => hsub hg⟩
  choose E hEf hE using key
  let U : (Ω ≃ₐ[K] Ω) → Set (Ω ≃ₐ[K] Ω) := fun i => {h | i⁻¹ * h ∈ (E i).fixingSubgroup}
  have hUo : ∀ i, IsOpen (U i) := by
    intro i
    haveI := hEf i
    exact (IntermediateField.fixingSubgroup_isOpen (E i)).preimage (continuous_const.mul continuous_id)
  have hUc : Set.univ ⊆ ⋃ i, U i := by
    intro h _
    refine Set.mem_iUnion.2 ⟨h, ?_⟩
    show h⁻¹ * h ∈ (E h).fixingSubgroup
    rw [inv_mul_cancel]
    exact one_mem _
  obtain ⟨S, hS⟩ := isCompact_univ.elim_finite_subcover U hUo hUc
  have hT : ∀ i, ∃ T : Finset Ω, ∀ g : Ω ≃ₐ[K] Ω, (∀ x ∈ T, g x = x) → g ∈ (E i).fixingSubgroup := by
    intro i
    haveI := hEf i
    exact mem_fixingSubgroup_of_fixes_finite_set K Ω (E i)
  choose T hT using hT
  refine ⟨S.biUnion T, fun s s' hs' => ?_⟩
  obtain ⟨i, hiS, hi⟩ := Set.mem_iUnion₂.1 (hS (Set.mem_univ s))
  have hi' : i⁻¹ * s ∈ (E i).fixingSubgroup := hi
  have hs'i : s' ∈ (E i).fixingSubgroup :=
    hT i s' (fun x hx => hs' x (Finset.mem_biUnion.2 ⟨i, hiS, hx⟩))
  have h1 := hE i _ (mul_mem hi' hs'i)
  have h2 := hE i _ hi'
  rw [← mul_assoc, mul_inv_cancel_left] at h1
  rw [mul_inv_cancel_left] at h2
  have h3 : f (s * s') - f s = (f (s * s') - f i) - (f s - f i) := by abel
  rw [h3]
  have := norm_sub_le (f (s * s') - f i) (f s - f i)
  linarith

theorem UpperTheory.V.Z.Kato.Joint.unif :
    UpperTheory.V.Z.Kato.Joint.Unif := by
  intro l _ Ω _ _ _ f hf δ hδ
  haveI : IsGalois ℚ Ω := inferInstance
  exact uniform_continuity_galois_group ℚ Ω f hf δ hδ
end

section

open UpperTheory.V.Z.Kato.Joint

private lemma smNz_unit {l : ℕ} [Fact l.Prime] {n : ℕ} (h : ¬ l ∣ n) : IsUnit (n : ZMod l) := by
  rw [isUnit_iff_ne_zero, Ne, ZMod.natCast_eq_zero_iff]
  exact h

private lemma smNz_norm {l : ℕ} [Fact l.Prime] (χ : DirichletCharacter ℂ l) {n : ℕ} (h : ¬ l ∣ n) :
    ‖χ (n : ZMod l)‖ = 1 := by
  have hu := smNz_unit (l := l) h
  have := χ.unit_norm_eq_one hu.unit
  rwa [IsUnit.unit_spec] at this

theorem UpperTheory.V.Z.Kato.Joint.smNz :
    UpperTheory.V.Z.Kato.Joint.SmNz := by
  intro l _ ι e N c d ψ a b hN hN0 hc0 hd0 hc hd ha hce hdb
  have hp : l.Prime := Fact.out
  refine ⟨?_, ?_⟩
  · intro i
    fin_cases i <;> simp [smT, hp.dvd_mul, hN, hc, hd]
  · simp only [Fin.sum_univ_four, smB, smT, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, map_mul,
      map_neg, map_pow, map_zpow₀, map_natCast, RingEquiv.apply_symm_apply, Nat.cast_mul,
      MulChar.inv_apply_eq_inv', mul_pow]
    have hC : (c : ℂ) ≠ 0 := by exact_mod_cast hc0.ne'
    have hD : (d : ℂ) ≠ 0 := by exact_mod_cast hd0.ne'
    have hNc : (N : ℂ) ≠ 0 := by exact_mod_cast hN0.ne'
    have hψN : ψ (N : ZMod l) ≠ 0 := by
      intro h0
      have := smNz_norm ψ hN
      rw [h0, norm_zero] at this
      exact zero_ne_one this
    have hψc : ψ (c : ZMod l) ≠ 0 := by
      intro h0
      have := smNz_norm ψ hc
      rw [h0, norm_zero] at this
      exact zero_ne_one this
    have hCe : (c : ℂ) ^ e ≠ 0 := pow_ne_zero _ hC
    have hw : (c : ℂ) ^ ((3 : ℤ) - ((2 * e + 1 : ℕ) : ℤ)) * (c : ℂ) ^ e = (c : ℂ) ^ 2 * ((c : ℂ) ^ e)⁻¹ := by
      rw [← zpow_natCast (c : ℂ) e, ← zpow_add₀ hC, ← zpow_natCast (c : ℂ) 2, ← zpow_neg,
        ← zpow_add₀ hC]
      congr 1
      push_cast
      ring
    set w := (c : ℂ) ^ ((3 : ℤ) - ((2 * e + 1 : ℕ) : ℤ)) with hwdef
    have hfac : (c : ℂ) ^ 2 * (d : ℂ) ^ 2 * (ψ (N : ZMod l))⁻¹ * (N : ℂ) ^ e +
        -(w * a * (d : ℂ) ^ 2) * (ψ (N : ZMod l) * ψ (c : ZMod l))⁻¹ * ((N : ℂ) ^ e * (c : ℂ) ^ e) +
        -((c : ℂ) ^ 2 * ((d : ℂ) * b)) * (ψ (N : ZMod l) * ψ (d : ZMod l))⁻¹ * ((N : ℂ) ^ e * (d : ℂ) ^ e) +
        w * a * ((d : ℂ) * b) * (ψ (N : ZMod l) * ψ (c : ZMod l) * ψ (d : ZMod l))⁻¹ *
          ((N : ℂ) ^ e * (c : ℂ) ^ e * (d : ℂ) ^ e) =
        (N : ℂ) ^ e * (ψ (N : ZMod l))⁻¹ *
          ((c : ℂ) ^ 2 - w * (c : ℂ) ^ e * a * (ψ (c : ZMod l))⁻¹) *
          ((d : ℂ) ^ 2 - (d : ℂ) * b * (d : ℂ) ^ e * (ψ (d : ZMod l))⁻¹) := by
      ring
    rw [hfac, hw]
    refine mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ hNc) (inv_ne_zero hψN)) ?_) ?_
    · have h1 : (c : ℂ) ^ 2 - (c : ℂ) ^ 2 * ((c : ℂ) ^ e)⁻¹ * a * (ψ (c : ZMod l))⁻¹ =
          (c : ℂ) ^ 2 * ((c : ℂ) ^ e)⁻¹ * ((c : ℂ) ^ e - a * (ψ (c : ZMod l))⁻¹) := by
        field_simp
      rw [h1]
      refine mul_ne_zero (mul_ne_zero (pow_ne_zero _ hC) (inv_ne_zero hCe)) ?_
      rw [sub_ne_zero]
      apply hce
      rw [norm_mul, norm_inv, ha, smNz_norm ψ hc]
      norm_num
    · intro h0
      apply hdb
      rw [zpow_neg_one, pow_succ]
      linear_combination h0
end

section

open UpperTheory.V.Z.Kato.Joint
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ

private theorem norm_l_lt_one (l : ℕ) [Fact l.Prime] : ‖((l : ℕ) : Qbar l)‖ < 1 := by
  have h : ((l : ℕ) : Qbar l) = algebraMap ℚ_[l] (PadicAlgCl l) ((l : ℕ) : ℚ_[l]) := by simp
  rw [h, PadicAlgCl.norm_extends]
  exact Padic.norm_p_lt_one

private theorem cg_scale {l : ℕ} [Fact l.Prime] (K : Qbar l) : ∃ N : ℕ, ∀ m, N ≤ m → ∀ (c₀ : ℕ) (u x y : Qbar l),
    ‖u‖ = 1 → Cg (2 * m) x y → Cg (m - c₀) (u * K * y) (u * K * x) := by
  have hl0 : 0 ≤ ‖((l : ℕ) : Qbar l)‖ := norm_nonneg _
  have hl1 := norm_l_lt_one l
  obtain ⟨N, hN⟩ : ∃ N : ℕ, ‖((l : ℕ) : Qbar l)‖ ^ N * ‖K‖ ≤ 1 := by
    rcases eq_or_ne ‖K‖ 0 with hK | hK
    · exact ⟨0, by rw [hK, mul_zero]; exact zero_le_one⟩
    · obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (inv_pos.2 (lt_of_le_of_ne (norm_nonneg K) (Ne.symm hK))) hl1
      refine ⟨N, ?_⟩
      have hKpos : 0 < ‖K‖ := lt_of_le_of_ne (norm_nonneg K) (Ne.symm hK)
      calc ‖((l : ℕ) : Qbar l)‖ ^ N * ‖K‖ ≤ ‖K‖⁻¹ * ‖K‖ :=
            mul_le_mul_of_nonneg_right hN.le hKpos.le
        _ = 1 := inv_mul_cancel₀ hK
  refine ⟨N, fun m hm c₀ u x y hu hxy => ?_⟩
  unfold Cg at hxy ⊢
  rw [norm_pow] at hxy ⊢
  have hdiff : u * K * y - u * K * x = -(u * K * (x - y)) := by ring
  rw [hdiff, norm_neg, norm_mul, norm_mul, hu, one_mul]
  have hmN : ‖((l : ℕ) : Qbar l)‖ ^ m ≤ ‖((l : ℕ) : Qbar l)‖ ^ N := pow_le_pow_of_le_one hl0 hl1.le hm
  have hmc : ‖((l : ℕ) : Qbar l)‖ ^ m ≤ ‖((l : ℕ) : Qbar l)‖ ^ (m - c₀) :=
    pow_le_pow_of_le_one hl0 hl1.le (Nat.sub_le m c₀)
  have hKm : ‖((l : ℕ) : Qbar l)‖ ^ m * ‖K‖ ≤ 1 :=
    le_trans (mul_le_mul_of_nonneg_right hmN (norm_nonneg K)) hN
  calc ‖K‖ * ‖x - y‖ ≤ ‖K‖ * ‖((l : ℕ) : Qbar l)‖ ^ (2 * m) :=
        mul_le_mul_of_nonneg_left hxy (norm_nonneg K)
    _ = (‖((l : ℕ) : Qbar l)‖ ^ m * ‖K‖) * ‖((l : ℕ) : Qbar l)‖ ^ m := by ring
    _ ≤ 1 * ‖((l : ℕ) : Qbar l)‖ ^ m :=
        mul_le_mul_of_nonneg_right hKm (pow_nonneg hl0 m)
    _ ≤ ‖((l : ℕ) : Qbar l)‖ ^ (m - c₀) := by rw [one_mul]; exact hmc

private theorem law_mono {Ω : Type} [Field Ω] [Algebra ℚ Ω] {l : ℕ} [Fact l.Prime] {A : ValuationSubring Ω} {c : Coef l}
    {Z : ∀ r : ℕ, G ℚ Ω → (ZMod (l ^ r))ˣ → Qbar l} {j : Ω →+* Qbar l} {m₀ m₁ c₀ : ℕ}
    {R : ∀ m : ℕ, DirichletCharacter (Qbar l) (l ^ m) → Qbar l → Qbar l} (hm : m₀ ≤ m₁) (h : HTLawCsOfCoef A c Z j m₀ c₀ R) :
    HTLawCsOfCoef A c Z j m₁ c₀ R := by
  obtain ⟨ζ, hζ, hlaw⟩ := h
  exact ⟨ζ, hζ, fun m hm' => hlaw m (hm.trans hm')⟩

open Classical in
private theorem cg_cases {l : ℕ} [Fact l.Prime] {κ₀ κ : Qbar l} (hκ : κ ≠ 0) : ∃ N : ℕ, ∀ m, N ≤ m →
    ∀ (c₀ : ℕ) (v a p s X b g w : Qbar l), ‖v‖ = 1 → ‖a‖ = 1 → p ^ 2 = 1 → s ^ 2 = 1 →
    (p = s → Cg (2 * m) X (κ * b * g * w)) → (p = -s → Cg (2 * m) X 0) →
    Cg (m - c₀) (if p = s then v * κ₀ * a ^ m * (b * g * w) else 0) (v * (κ₀ / κ) * a ^ m * X) := by
  obtain ⟨N, hN⟩ := cg_scale (κ₀ / κ)
  refine ⟨N, fun m hm c₀ v a p s X b g w hv ha hp hs h1 h2 => ?_⟩
  have hu : ‖v * a ^ m‖ = 1 := by rw [norm_mul, norm_pow, hv, ha, one_pow, one_mul]
  by_cases hE : p = s
  · rw [if_pos hE]
    have h3 := hN m hm c₀ (v * a ^ m) X (κ * b * g * w) hu (h1 hE)
    have e1 : v * a ^ m * (κ₀ / κ) * (κ * b * g * w) = v * κ₀ * a ^ m * (b * g * w) := by
      field_simp
    have e2 : v * a ^ m * (κ₀ / κ) * X = v * (κ₀ / κ) * a ^ m * X := by ring
    rw [e1, e2] at h3
    exact h3
  · have hps : p ^ 2 = s ^ 2 := by rw [hp, hs]
    have hO : p = -s := (sq_eq_sq_iff_eq_or_eq_neg.1 hps).resolve_left hE
    rw [if_neg hE]
    have h3 := hN m hm c₀ (v * a ^ m) X 0 hu (h2 hO)
    have e2 : v * a ^ m * (κ₀ / κ) * X = v * (κ₀ / κ) * a ^ m * X := by ring
    rw [mul_zero, e2] at h3
    exact h3

theorem UpperTheory.V.Z.Kato.Joint.pinOf :
    UpperTheory.V.Z.Kato.Joint.PinOf := by
  intro hM hU hMo l _ Ω _ _ ι e A W c ν Z j u w ψ α B cc v n β t hl he hα hj hν hσ hμ hv ht hne hE
  obtain ⟨cO, L, κ, φ, n₀, r₁, hκ, hL, hφ, h1, h2, h3⟩ :=
    hM l ι e _ u w ψ α B cc v n β t hl he rfl hμ hv ht hne
  obtain ⟨c', hc, hcO, -⟩ := hU l c cO ∅ (fun x hx => absurd hx (Finset.notMem_empty x))
  obtain ⟨κ₀, vv, m₀, c₀, hκ₀, hvv, hH⟩ := hE
  obtain ⟨σ, hσ1, hσ2, hσ3⟩ := hσ
  obtain ⟨N, hN⟩ := cg_cases (κ₀ := κ₀) hκ
  have hH' := law_mono (le_max_left m₀ (max N 1)) ((hMo l Ω c c' hc).2.2 A Z j m₀ c₀ _ hH)
  refine ⟨c', hc, ?_⟩
  unfold Pin7
  refine ⟨ν σ, ι.symm α, κ₀ / κ, vv, j, _, L, φ, max m₀ (max N 1), c₀, n₀, hν, ⟨σ, hσ1, hσ2, rfl⟩, hσ3, hα, hvv,
    div_ne_zero hκ₀ hκ, hj, fun k => hcO (hL k), hH', ?_, ?_, r₁, h3⟩
  · intro m hm ψ' _ z hz
    have hm1 : 1 ≤ m := by omega
    have hmN : N ≤ m := by omega
    have ha : ψ' (-1) ^ 2 = 1 := by rw [← map_pow, neg_one_sq, map_one]
    have hb : (ι.symm ((-1) ^ e * ψ (-1))) ^ 2 = 1 := by
      rw [← map_pow, mul_pow, ← map_pow, ← pow_mul, mul_comm e 2, pow_mul, neg_one_sq, neg_one_sq, one_pow, map_one,
        one_mul, map_one]
    exact hN m hmN c₀ _ _ _ _ _ _ _ _ (hvv m).1 hα ha hb (fun hs => h1 m hm1 ψ' hs z hz) (fun hs => h2 m hm1 ψ' hs z hz)
  · intro r _ x
    apply ι.injective
    rw [map_inv₀, hφ, MulChar.inv_apply_eq_inv', inv_inv]
    exact ι.apply_symm_apply _
end

section

open UpperTheory.V.Z.Kato.Joint

theorem UpperTheory.V.Z.Kato.Joint.mono :
    UpperTheory.V.Z.Kato.Joint.Mono := by
  intro l _ Ω _ _ c c' h
  refine ⟨?_, ?_, ?_⟩
  · rintro W y S' ⟨h1, h2, h3, h4, h5⟩
    refine ⟨fun s i j => h (h1 s i j), h2, fun s i => h (h3 s i), h4, fun n hn w hw hd ψ hk hs => ?_⟩
    obtain ⟨Y, P, u, b, a1, a2, a3, a4, a5, a6, a7, a8, a9⟩ := h5 n hn w hw hd ψ hk hs
    refine ⟨Y, P, u, b, a1, fun s x i => h (a2 s x i), h a3, a4, fun i => h (a5 i), a6, a7, a8, fun q hq hl => ?_⟩
    obtain ⟨B, hB, t, ht, ht'⟩ := a9 q hq hl
    exact ⟨B, hB, t, fun x i => h (ht x i), ht'⟩
  · rintro A ν Z ⟨h1, h2, h3⟩
    exact ⟨h1, fun r => ⟨fun s x => h ((h2 r).1 s x), (h2 r).2⟩, h3⟩
  · rintro A Z j m₀ c₀ Rhs ⟨ζ, hζ, H⟩
    refine ⟨ζ, hζ, fun m hm => ?_⟩
    obtain ⟨ι, inst, P, o, ⟨p1, p2, p3, p4, p5⟩, hc⟩ := H m hm
    exact ⟨ι, inst, P, o, ⟨p1, p2, fun i => h (p3 i), p4, p5⟩, hc⟩
end

section

open UpperTheory.V.Z.Kato.Joint

private theorem norm_le_of_pow {l : ℕ} [Fact l.Prime] (ι : PadicAlgCl l ≃+* ℂ) (z : ℂ) (n : ℕ) (hn : n ≠ 0)
    (h : z ^ n = 1) : ‖ι.symm z‖ ≤ 1 := by
  have h1 : ‖ι.symm z‖ ^ n = 1 := by rw [← norm_pow, ← map_pow, h, map_one, norm_one]
  exact ((pow_eq_one_iff_of_nonneg (norm_nonneg _) hn).mp h1).le

private theorem hat_std {N : ℕ} [NeZero N] (φ : ZMod N → ℂ) (d : ℤ) :
    GlobalTheory.EisM.hat φ d = ∑ y : ZMod N, φ y * ZMod.stdAddChar (y * (d : ZMod N)) := by
  unfold GlobalTheory.EisM.hat
  refine Finset.sum_nbij' (fun i => (i : ZMod N)) (fun y => y.val) (fun _ _ => Finset.mem_univ _)
    (fun y _ => Finset.mem_range.mpr (ZMod.val_lt y)) (fun i hi => ZMod.val_cast_of_lt (Finset.mem_range.mp hi))
    (fun y _ => ZMod.natCast_zmod_val y) (fun i _ => ?_)
  have h : ((i : ZMod N)) * (d : ZMod N) = (((i : ℤ) * d : ℤ) : ZMod N) := by push_cast; rfl
  rw [h, ZMod.stdAddChar_coe]
  push_cast
  rfl

private theorem norm_two' {l : ℕ} [hl : Fact l.Prime] (h : l ≠ 2) : ‖(2 : PadicAlgCl l)‖ = 1 := by
  have h1 : (2 : PadicAlgCl l) = algebraMap ℚ_[l] (PadicAlgCl l) ((2 : ℕ) : ℚ_[l]) := by
    rw [map_natCast]; rfl
  rw [h1, norm_algebraMap']
  exact Padic.norm_natCast_eq_one_iff.mpr ((Nat.coprime_primes hl.out Nat.prime_two).mpr h)

theorem UpperTheory.V.Z.Kato.Joint.hatW :
    UpperTheory.V.Z.Kato.Joint.HatW := by
  intro l _ ι N _ θ hl
  refine ⟨?_, fun d => ?_, fun d => ?_⟩
  · by_contra hc
    push Not at hc
    have h0 : ZMod.dft (fun y : ZMod N => θ y) = 0 := by
      funext k
      have := hc (-k)
      rw [hat_std] at this
      rw [ZMod.dft_apply, Pi.zero_apply, ← this]
      refine Finset.sum_congr rfl fun y _ => ?_
      simp [mul_comm]
    have h1 := congrFun ((LinearEquiv.map_eq_zero_iff _).mp h0) 1
    simp at h1
  · have h2 : ι.symm 2 = 2 := map_ofNat _ 2

    rw [map_div₀, norm_div, h2, norm_two' hl, div_one, hat_std, map_sum]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun y _ => ?_
    rw [map_mul, norm_mul]
    refine mul_le_one₀ ?_ (norm_nonneg _) ?_
    · by_cases hy : IsUnit y
      · obtain ⟨u, rfl⟩ := hy
        refine norm_le_of_pow ι _ (Fintype.card (ZMod N)ˣ) Fintype.card_ne_zero ?_
        rw [← map_pow, ← Units.val_pow_eq_pow_val, pow_card_eq_one, Units.val_one, map_one]
      · rw [MulChar.map_nonunit _ hy]; simp
    · refine norm_le_of_pow ι _ N (NeZero.ne N) ?_
      rw [← AddChar.map_nsmul_eq_pow]
      simp
  · rw [hat_std, hat_std]
    simp
end

section

open UpperTheory.V.Z.Kato.Joint

theorem UpperTheory.V.Z.Kato.Joint.rhoFrob :
    UpperTheory.V.Z.Kato.Joint.RhoFrob := by
  intro l _ Ω _ _ _ ι e S A W g χ hN _ hatt ρ hρ
  have h : ∀ s, (ρ s : Matrix (Fin 2) (Fin 2) (Formalism.ConjugateSelfDual.Qbar l)) = _ := fun s =>
    (hρ s).trans (GlobalTheory.RhoAdm.untw_val' e W χ s).symm
  refine ⟨?_, fun V hV => GlobalTheory.RhoAdm.untw_irr e W χ hN.irr V fun s v hv => ?_⟩
  · obtain ⟨S0, hS0⟩ := GlobalTheory.RhoAdm.frob_trace_det ι e W g χ hatt
    refine ⟨S0, fun q hq hqS s hs => ?_⟩
    rw [h s]
    exact hS0 q hq hqS s hs
  · rw [← h s]
    exact hV s v hv
end

section

open UpperTheory.V.Z.Kato.Joint

theorem UpperTheory.V.Z.Kato.Joint.jEx :
    UpperTheory.V.Z.Kato.Joint.JEx := by
  intro l _ Ω _ _ _ A hA
  obtain ⟨v, hv, hl⟩ := hA
  have hAl : A.valuation ((l : ℕ) : Ω) < 1 := by
    have := (hv ((l : ℕ) : NumberField.RingOfIntegers ℚ)).2 hl
    simpa using this
  exact ⟨(ValuationSubring.mem_nonunits_iff _).2 hAl, Formalism.BasicNotions.Examples₂.LB.exists_emb A hAl⟩
end
