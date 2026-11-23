module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.Bundle002
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.CoeffSlD
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle008
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SlMulToRingEquiv
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.DiamEx
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.KmapComp
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.K4 GlobalTheory.KA UpperTheory.Kd.K4 UpperTheory.V.Z.Kato.Sym UpperTheory.V.Z.Kato.Nb
open scoped Matrix MatrixGroups Classical

private theorem nle {l : ℕ} [Fact l.Prime] (c : Coef l) {a : Qbar l} (ha : a ∈ c.O) : ‖a‖ ≤ 1 := by
  have hi : IsIntegral ℤ_[l] a := (Algebra.IsIntegral.isIntegral (R := ℤ_[l]) (⟨a, ha⟩ : c.O)).map c.O.val
  have hq : IsIntegral ℚ_[l] a := Algebra.IsIntegral.isIntegral a
  change spectralValue (minpoly ℚ_[l] a) ≤ 1
  rw [spectralValue_le_one_iff (minpoly.monic hq)]
  intro k
  rw [minpoly.isIntegrallyClosed_eq_field_fractions' ℚ_[l] hi, Polynomial.coeff_map]
  exact PadicInt.norm_le_one _

private theorem inv_mem_O {l : ℕ} [Fact l.Prime] (c : Coef l) {p : ℕ} (hp : Nat.Coprime l p) :
    ((p : Qbar l))⁻¹ ∈ c.O := by
  have hu : IsUnit (p : ℤ_[l]) := by
    rw [PadicInt.isUnit_iff, PadicInt.norm_natCast_eq_one_iff]
    exact hp
  obtain ⟨v, hv⟩ := hu.exists_right_inv
  have h := congrArg (algebraMap ℤ_[l] (Qbar l)) hv
  rw [map_mul, map_natCast, map_one] at h
  rw [← eq_inv_of_mul_eq_one_right h]
  exact c.O.algebraMap_mem v

theorem UpperTheory.V.Z.Kato.Nb.sEulCg :
    UpperTheory.V.Z.Kato.Nb.SEulCg := by
  intro l hl Ω _ _ _ ι e gN A W ε X pr N _ x c d gm ψ cf _ _ p n hp hn hd a δ ha hδ
  obtain ⟨k, hk⟩ := hd
  have hpk : p = l ^ n * k + 1 := by have := hp.pos; omega
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hcop : Nat.Coprime l p := by
    rw [hpk, pow_succ', mul_assoc]
    simp
  have hq := inv_mem_O cf hcop
  have hp0 : (p : Qbar l) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
  refine ⟨?_, ?_⟩
  · unfold eul
    rw [← inv_pow, ← inv_pow]
    exact add_mem (sub_mem (one_mem _) (mul_mem ha (pow_mem hq _))) (mul_mem hδ (pow_mem hq _))
  intro σ hψ he htr hdet
  have hc : (cyclotomicCharacter Ω l σ.toRingEquiv : ℤ_[l]) = p := by
    apply Subtype.val_injective
    apply (algebraMap ℚ_[l] (Qbar l)).injective
    have h : eps l σ = algebraMap ℚ_[l] (Qbar l) ((cyclotomicCharacter Ω l σ.toRingEquiv : ℤ_[l]) : ℚ_[l]) := rfl
    rw [he] at h
    refine h.symm.trans ?_
    simp
  have hm : ((((cycMod (F := ℚ) (Ω := Ω) l 1 σ : ZMod (l ^ 1))).val : ℕ) : ZMod l) = 1 := by
    have h : ((cycMod ℚ Ω l 1 σ : (ZMod (l ^ 1))ˣ) : ZMod (l ^ 1)) =
      PadicInt.toZModPow 1 (cyclotomicCharacter Ω l σ.toRingEquiv : ℤ_[l]) := rfl
    rw [h, hc, map_natCast, ZMod.val_natCast, pow_one, ZMod.natCast_mod, hpk]
    simp
  have hth : thK l e ψ σ = ((p : Qbar l) ^ e)⁻¹ := by
    unfold thK
    rw [hm, hψ, he, mul_one]
  unfold rhoK at htr hdet
  rw [hth, inv_inv] at htr hdet
  rw [Matrix.trace_smul, Matrix.trace_fin_two, smul_eq_mul] at htr
  rw [Matrix.det_smul, Fintype.card_fin, ← pow_mul, mul_comm e 2, Matrix.det_fin_two] at hdet
  have hdet' := mul_left_cancel₀ (pow_ne_zero _ hp0) hdet
  have hpc : (p : Qbar l) = (l : Qbar l) ^ (m + 1) * k + 1 := by exact_mod_cast hpk
  have ho : (k : Qbar l) * (a * (p : Qbar l)⁻¹ ^ (e + 1) - δ * (p : Qbar l)⁻¹ ^ 2 * (1 + p)) ∈ cf.O :=
    mul_mem (natCast_mem _ _) (sub_mem (mul_mem ha (pow_mem hq _))
      (mul_mem (mul_mem hδ (pow_mem hq _)) (add_mem (one_mem _) (natCast_mem _ _))))
  have key : eul l e p a δ - 1 * (mat W σ - 1).det =
      (l : Qbar l) ^ (m + 1) * ((k : Qbar l) * (a * (p : Qbar l)⁻¹ ^ (e + 1) - δ * (p : Qbar l)⁻¹ ^ 2 * (1 + p))) := by
    rw [← mul_assoc, ← sub_eq_of_eq_add hpc, Matrix.det_fin_two]
    simp only [Matrix.sub_apply, Matrix.one_apply_eq, Matrix.one_apply_ne (show (0 : Fin 2) ≠ 1 by decide),
      Matrix.one_apply_ne (show (1 : Fin 2) ≠ 0 by decide), sub_zero]
    unfold eul
    rw [← htr, ← hdet']
    simp only [inv_pow]
    field_simp
    ring
  unfold GlobalTheory.Ord2.Cg
  rw [key, norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) (nle cf ho)
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.K4 GlobalTheory.KA UpperTheory.Kd.K4 UpperTheory.V.Z.Kato.Sym UpperTheory.V.Z.Kato.Nb
open scoped Matrix MatrixGroups Classical

namespace UpperTheory.V.Z.Kato.Nb.PushforwardPsi

private theorem exF {Γ A C : Type} [Group Γ] [CommGroup A] [CommGroup C] (c : Γ →* A) (ψ : Γ →* C)
    (h : ∀ s, c s = 1 → ψ s = 1) : ∃ f : A → C, ∀ a s, f (a * (c s)⁻¹) = f a * ψ s := by
  have h1 : ∀ a : A, ∃ s, c s = a⁻¹ * (QuotientGroup.mk a : A ⧸ c.range).out := fun a =>
    QuotientGroup.eq.1 (QuotientGroup.out_eq' (QuotientGroup.mk a : A ⧸ c.range)).symm
  choose σ hσ using h1
  refine ⟨fun a => ψ (σ a), fun a s => ?_⟩
  have e : (QuotientGroup.mk (a * (c s)⁻¹) : A ⧸ c.range) = QuotientGroup.mk a :=
    QuotientGroup.eq.2 ⟨s, by simp⟩
  have h2 := h ((σ (a * (c s)⁻¹))⁻¹ * (σ a * s)) (by
    rw [map_mul, map_mul, map_inv, hσ, hσ, e, inv_mul_eq_one, mul_inv, inv_inv, mul_right_comm])
  rw [map_mul, map_inv, inv_mul_eq_one, map_mul] at h2
  exact h2

private theorem exC (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (M : ℕ) [NeZero M] :
    ∃ c : (Ω ≃ₐ[ℚ] Ω) →* (ZMod M)ˣ, ∀ s, cycM M s = c s ∧ ∀ z : Ω, z ^ M = 1 → s z = z ^ (c s : ZMod M).val := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : CharZero Ω := algebraRat.charZero Ω
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω M
  refine ⟨hζ.autToPow ℚ, fun s => ?_⟩
  have hs : ∀ z : Ω, z ^ M = 1 → s z = z ^ (hζ.autToPow ℚ s : ZMod M).val := fun w hw => by
    obtain ⟨i, -, rfl⟩ := hζ.eq_pow_of_pow_eq_one hw
    rw [map_pow, ← hζ.autToPow_spec ℚ s, ← pow_mul, ← pow_mul, mul_comm]
  refine ⟨?_, hs⟩
  have hM := cycM_spec M s ⟨_, hs⟩
  apply Units.ext
  apply ZMod.val_injective
  exact hζ.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) ((hM ζ hζ.pow_eq_one).symm.trans (hs ζ hζ.pow_eq_one))

private theorem push_prod {Γ A B B' V : Type} [Group Γ] [AddCommMonoid V] [Fintype A] [Fintype B'] [DecidableEq B]
    {i1 : Fintype (A × B')} {i2 : DecidableEq (A × B)} (g : B' → B) (Z : Γ → A × B' → V) (s : Γ) (a : A) (y : B) :
    @push Γ (A × B) (A × B') i1 i2 V _ (Prod.map id g) Z s (a, y) = ∑ y', if g y' = y then Z s (a, y') else 0 := by
  obtain rfl : i1 = instFintypeProd A B' := Subsingleton.elim _ _
  unfold push
  rw [Finset.sum_filter, Fintype.sum_prod_type_right]
  refine Finset.sum_congr rfl fun y' _ => ?_
  by_cases h : g y' = y <;> simp [h]

end UpperTheory.V.Z.Kato.Nb.PushforwardPsi

open UpperTheory.V.Z.Kato.Nb.PushforwardPsi in
theorem UpperTheory.V.Z.Kato.Nb.sPushPsi :
    UpperTheory.V.Z.Kato.Nb.SPushPsi := by
  intro l _ Ω _ _ _ cf ρ p n _ ψw hψ Y hc hp hcont hO
  obtain ⟨c, hcs⟩ := exC Ω p
  obtain ⟨f, hf⟩ := exF c ψw fun s hs => hψ s fun z hz => by
    rw [(hcs s).2 z hz, hs, Units.val_one, ZMod.val_one_eq_one_mod, ← pow_eq_pow_mod _ hz, pow_one]
  refine ⟨fun r s x => ∑ t, if f t = x.1 then Y r s (t, x.2) else 0, fun r s s' x => ?_, fun r x i => ?_,
    fun r s x i => ?_, fun r s => ?_, fun r s y => ?_⟩
  · have e : ∑ t, (if f t = (x * (ψw.prod (cycMod ℚ Ω l r)⁻¹) s).1 then
        Y r s' (t, (x * (ψw.prod (cycMod ℚ Ω l r)⁻¹) s).2) else 0) =
        ∑ t, if f t = x.1 then Y r s' ((t, x.2) * cycT l r p s) else 0 := by
      symm
      refine Fintype.sum_equiv (Equiv.mulRight (c s)⁻¹) _ _ fun t => ?_
      simp [hf, cycT, (hcs s).1]
    beta_reduce
    rw [e, Matrix.mulVec_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun t _ => ?_
    split_ifs
    · exact hc r s s' _
    · simp
  · simp only [Finset.sum_apply]
    refine continuous_finsetSum _ fun t _ => ?_
    split_ifs
    · exact hcont r _ i
    · exact continuous_const
  · simp only [Finset.sum_apply]
    refine sum_mem fun t _ => ?_
    split_ifs
    · exact hO r s _ i
    · exact zero_mem _
  · funext ⟨a, y⟩
    rw [push_prod]
    have e : ∀ t, Y r s (t, y) = ∑ y', if redL l r y' = y then Y (r + 1) s (t, y') else 0 := fun t => by
      rw [hp r, push_prod]
    simp only [e]
    have e2 : ∀ (P : Prop) [Decidable P] {ι : Type} [Fintype ι] (v : ι → Fin 2 → Qbar l),
        (if P then ∑ j, v j else 0) = ∑ j, if P then v j else 0 := fun P _ _ _ v => by split_ifs <;> simp
    simp only [e2]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun y' _ => Finset.sum_congr rfl fun t _ => ?_
    change (if f t = a then if redL l r y' = y then _ else 0 else 0) = if redL l r y' = y then if f t = a then _ else 0 else 0
    split_ifs <;> rfl
  · rw [Finset.sum_comm]
    simp
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.K4 GlobalTheory.KA UpperTheory.Kd.K4 UpperTheory.V.Z.Kato.Sym UpperTheory.V.Z.Kato.Nb
open scoped Matrix MatrixGroups Classical

private theorem lsq_eq (l p L : ℕ) (h : Nat.Coprime p l) : lsqInv l p L = inv1 p l ^ (2 * L) := by
  have h1 : IsUnit (l : ZMod p) := (ZMod.isUnit_iff_coprime l p).2 h.symm
  have h2 : IsUnit ((l : ZMod p) ^ (2 * L)) := h1.pow _
  unfold lsqInv inv1
  rw [dite_eq_left h1, dite_eq_left h2, inv_pow]
  congr 1
  ext
  simp

private theorem arg_mem {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (M : ℕ) [NeZero M]
    (s : Ω ≃ₐ[ℚ] Ω) (y : (ZMod M)ˣ) : (repM M y)⁻¹ * s * repM M (y * (cycM M s)⁻¹) ∈ fixMu Ω M := by
  obtain ⟨-, -, -, -, -, -, -, hM⟩ := sSlD Ω ε X 1 one_pos
  have mul : ∀ a b : Ω ≃ₐ[ℚ] Ω, cycM M (a * b) = cycM M a * cycM M b := fun a b => (hM M a).2.1 b
  have rep : ∀ y : (ZMod M)ˣ, cycM M (repM (Ω := Ω) M y) = y := (hM M s).2.2.1
  let f : (Ω ≃ₐ[ℚ] Ω) →* (ZMod M)ˣ := MonoidHom.mk' (cycM M) mul
  rw [(hM M _).2.2.2.1]
  have e : f ((repM M y)⁻¹ * s * repM M (y * (cycM M s)⁻¹)) = 1 := by
    simp only [map_mul, map_inv]
    change (cycM M (repM (Ω := Ω) M y))⁻¹ * cycM M s * cycM M (repM (Ω := Ω) M (y * (cycM M s)⁻¹)) = 1
    rw [rep, rep, mul_comm y, ← mul_assoc, mul_inv_cancel_right, inv_mul_cancel]
  exact e

private theorem lift_push {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (l : ℕ) [Fact l.Prime]
    (N w n c M : ℕ) [NeZero N] [NeZero M] {T ι : Type} [DecidableEq T] [Fintype ι] (π : (ZMod M)ˣ → T)
    (z : ι → (Ω ≃ₐ[ℚ] Ω) → X.Fn l) (bB : (Ω ≃ₐ[ℚ] Ω) → X.Fn l)
    (h : ∀ σ ∈ fixMu Ω M, LiftB X l N w n c (∑ i, z i σ) (bB σ)) (s : Ω ≃ₐ[ℚ] Ω) (t : T) :
    LiftB X l N w n c (∑ i, GlobalTheory.KA.push π (shB X l M (z i)) s t) (GlobalTheory.KA.push π (shB X l M bB) s t) := by
  obtain ⟨-, -, -, hSum, -, -, hGal, -⟩ := sApi Ω ε X l n
  have hN : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have key : ∀ y : (ZMod M)ˣ, LiftB X l N w n c (∑ i, shB X l M (z i) s y) (shB X l M bB s y) := by
    intro y
    have hy := h _ (arg_mem X M s y)
    refine ⟨(sBStab Ω ε X l N w hN _ hy.1).1 _, ?_⟩
    have hc : CgF X l n (bB ((repM M y)⁻¹ * s * repM M (y * (cycM M s)⁻¹)))
        ((l : ℤ_[l]) ^ c • ∑ i, z i ((repM M y)⁻¹ * s * repM M (y * (cycM M s)⁻¹))) := hy.2
    have hg := hGal (repM M y) _ _ hc
    have e : (l : ℤ_[l]) ^ c • ∑ i, shB X l M (z i) s y = X.galB l (repM M y)
        ((l : ℤ_[l]) ^ c • ∑ i, z i ((repM M y)⁻¹ * s * repM M (y * (cycM M s)⁻¹))) := by

      simp only [shB, map_smul, map_sum]
    intro u
    have hu := hg u
    rw [← e] at hu
    exact hu
  have hpush : ∀ Y : (Ω ≃ₐ[ℚ] Ω) → (ZMod M)ˣ → X.Fn l,
      GlobalTheory.KA.push π Y s t = ∑ y ∈ Finset.univ.filter (fun y => π y = t), Y s y := fun Y => rfl
  simp only [hpush]
  rw [Finset.sum_comm]
  refine ⟨Submodule.sum_mem _ (fun y _ => (key y).1), ?_⟩
  have hs := hSum _ (Finset.univ.filter (fun y => π y = t)) (fun y => shB X l M bB s y)
    (fun y => (l : ℤ_[l]) ^ c • ∑ i, shB X l M (z i) s y) (fun y _ => (key y).2)
  rw [← Finset.smul_sum] at hs
  exact hs

theorem UpperTheory.V.Z.Kato.Nb.sRelT :
    UpperTheory.V.Z.Kato.Nb.SRelT := by
  intro l _ Ω _ _ _ ι e gN A W ε X pr N _ x c d gm ψ cf hA he p _ hp c₀ Y hY r n
  obtain ⟨bB, hB, b, hb, hC⟩ := hY r n
  obtain ⟨-, -, -, -, hadd, -, -, hgal, -⟩ := hA
  have hw : 2 * e + 1 - 2 = 2 * e - 1 := by omega
  have hB' : ∀ σ ∈ fixMu Ω (lvT l n r N p), LiftB X l N (2 * e - 1) n c₀ (∑ r₀, clsT X l n r N p x c d (2 * e - 1) (gm r₀) σ) (bB σ) := by
    intro σ hσ
    rw [← hw]
    exact hB σ hσ
  refine ⟨fun s y => GlobalTheory.KA.push (rdT l n r N p) (shB X l (lvT l n r N p) bB) s (y.1 * inv1 p l ^ (2 * (r + n)), y.2), b,
    fun s y => lift_push X l N _ n c₀ _ (rdT l n r N p) _ bB hB' s _, hb, fun s y => ?_⟩
  have key : ∀ t, pr (GlobalTheory.KA.push (rdT l n r N p) (shB X l (lvT l n r N p) bB) s t) = YfBT X l pr W e ψ n r N p bB s t := by
    intro t
    have hs := map_sum (AddMonoidHom.mk' pr hadd) (shB X l (lvT l n r N p) bB s)
      (Finset.univ.filter fun y' => rdT l n r N p y' = t)
    refine hs.trans (Finset.sum_congr rfl fun y' _ => ?_)
    exact hgal _ _ (hB' _ (arg_mem X _ s y')).1
  have := hC s y
  rw [lsq_eq l p _ hp, ← key] at this
  exact this
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.K4 GlobalTheory.KA UpperTheory.Kd.K4 UpperTheory.V.Z.Kato.Sym UpperTheory.V.Z.Kato.Nb
open scoped Matrix MatrixGroups Classical

namespace UpperTheory.V.Z.Kato.Nb

open CongruenceSubgroup

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (l : ℕ) [Fact l.Prime]

private theorem dc_fix (N w : ℕ) (γ : SL(2, ℤ)) (hγ : γ ∈ Gam N l) (b : X.Fn l) (hb : b ∈ X.B N l w) :
    X.act l (γ : Matrix (Fin 2) (Fin 2) ℤ) b = b := by
  unfold Tower.B at hb
  induction hb using Submodule.span_induction with
  | mem x hx => exact hx.2 γ hγ
  | zero => exact map_zero _
  | add x y _ _ hx hy => rw [map_add (f := _), hx, hy]
  | smul a x _ hx => rw [map_smul, hx]

private theorem dc_mul (σ τ : SL(2, ℤ)) (b : X.Fn l) :
    X.act l (τ : Matrix (Fin 2) (Fin 2) ℤ) (X.act l (σ : Matrix (Fin 2) (Fin 2) ℤ) b) =
      X.act l ((σ * τ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) b := by
  rw [Tower.act_act Ω ε X l _ _ (by rw [σ.2]; norm_num) (by rw [τ.2]; norm_num),
    Matrix.SpecialLinearGroup.coe_mul]

private theorem dc_en (N : ℕ) (σ τ : SL(2, ℤ)) (hσ : σ ∈ Gamma0 N) (hτ : τ ∈ Gamma0 N) :
    (en (σ * τ) 1 1 : ZMod N) = (en σ 1 1 : ZMod N) * (en τ 1 1 : ZMod N) := by
  have h0 := Gamma0_mem.1 hσ
  simp only [en, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
  push_cast
  rw [h0]
  ring

private theorem dc_same (N w : ℕ) (σ τ : SL(2, ℤ)) (hσ : σ ∈ Gamma0 N ⊓ Gamma0 l) (hτ : τ ∈ Gamma0 N ⊓ Gamma0 l)
    (h : (en σ 1 1 : ZMod N) = (en τ 1 1 : ZMod N)) (b : X.Fn l) (hb : b ∈ X.B N l w) :
    X.act l (σ : Matrix (Fin 2) (Fin 2) ℤ) b = X.act l (τ : Matrix (Fin 2) (Fin 2) ℤ) b := by
  obtain ⟨ρ, hρ⟩ : ∃ ρ, ρ = τ * σ⁻¹ := ⟨_, rfl⟩
  have hτ' : τ = ρ * σ := by rw [hρ, inv_mul_cancel_right]
  have hρ0 : ρ ∈ Gamma0 N ⊓ Gamma0 l := by
    rw [hρ]
    exact Subgroup.mul_mem _ hτ (Subgroup.inv_mem _ hσ)
  have det1 : ∀ B : SL(2, ℤ), B ∈ Gamma0 N → (en B 0 0 : ZMod N) * (en B 1 1 : ZMod N) = 1 := by
    intro B hB
    have h0 := Gamma0_mem.1 hB
    have hd := congrArg (fun z : ℤ => (z : ZMod N)) B.2
    simp only [Matrix.det_fin_two] at hd
    push_cast at hd
    rw [h0, mul_zero, sub_zero] at hd
    exact hd
  have hσ11 : (en σ⁻¹ 1 1 : ZMod N) = (en σ 0 0 : ZMod N) := by
    simp [en, Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
  have hρ11 : (en ρ 1 1 : ZMod N) = 1 := by
    rw [hρ, dc_en N τ σ⁻¹ hτ.1 (Subgroup.inv_mem _ hσ.1), ← h, hσ11, mul_comm]
    exact det1 σ hσ.1
  have hρ00 : (en ρ 0 0 : ZMod N) = 1 := by
    have := det1 ρ hρ0.1
    rw [hρ11, mul_one] at this
    exact this
  have hρG : ρ ∈ Gam N l := ⟨(Gamma1_mem _ _).2 ⟨hρ00, hρ11, Gamma0_mem.1 hρ0.1⟩, hρ0.2⟩
  rw [hτ', ← dc_mul X l ρ σ b, dc_fix X l N w ρ hρG b hb]

end UpperTheory.V.Z.Kato.Nb

theorem UpperTheory.V.Z.Kato.Nb.sDiamChar :
    UpperTheory.V.Z.Kato.Nb.SDiamChar := by
  unfold SDiamChar
  intro l _ Ω _ _ _ ι e gN A W ε X pr N _ x c d gm ψ cf hA he hlN hb
  obtain ⟨-, -, -, -, -, -, -, -, ⟨δ, hδ⟩, -⟩ := hA
  obtain ⟨b0, hb0, hne⟩ := hb
  have hl : l.Prime := Fact.out
  have hN0 : N ≠ 0 := NeZero.ne N
  have hNpos : 0 < N := Nat.pos_of_ne_zero hN0
  have hdiam : ∀ (q : ℕ) (b : X.Fn l),
      X.diam N l q b = X.act l (sgD N l q : Matrix (Fin 2) (Fin 2) ℤ) b := fun q b => rfl
  have hcop : ∀ q : ℕ, q.Prime → ¬ q ∣ l * N → q.Coprime N := fun q hq hd =>
    (Nat.Prime.coprime_iff_not_dvd hq).2 (fun h => hd (Dvd.dvd.mul_left h l))
  have hisD : ∀ q : ℕ, q.Prime → ¬ q ∣ l * N → IsDiam N l q (sgD N l q) :=
    fun q hq hd => Betti.isDiam_sgD hN0 hl.ne_zero (hcop q hq hd)
  have hpr : ∀ q : ℕ, q.Prime → ¬ q ∣ l * N → ∀ b ∈ X.B N l (2 * e - 1),
      pr (X.act l (sgD N l q : Matrix (Fin 2) (Fin 2) ℤ) b) = δ q • pr b :=
    fun q hq hd b hb => (hδ q hq hd b hb).2
  have cancel : ∀ a a' : Qbar l, a • pr b0 = a' • pr b0 → a = a' :=
    fun a a' h => smul_left_injective (Qbar l) hne h
  have hQ : ∀ u : (ZMod N)ˣ, ∃ q > l * N, q.Prime ∧ (q : ZMod N) = u :=
    fun u => Nat.forall_exists_prime_gt_and_eq_mod u.isUnit (l * N)
  choose Q hQgt hQp hQu using hQ
  have hQd : ∀ u, ¬ Q u ∣ l * N := fun u h => by
    have h1 := Nat.le_of_dvd (Nat.mul_pos hl.pos hNpos) h
    have h2 := hQgt u
    omega
  have mem : ∀ u, sgD N l (Q u) ∈ CongruenceSubgroup.Gamma0 N ⊓ CongruenceSubgroup.Gamma0 l :=
    fun u => (hisD _ (hQp u) (hQd u)).1
  have en_u : ∀ u, (en (sgD N l (Q u)) 1 1 : ZMod N) = u := fun u => by
    rw [(hisD _ (hQp u) (hQd u)).2, hQu]
  have inB : ∀ u (b : X.Fn l), b ∈ X.B N l (2 * e - 1) →
      X.act l (sgD N l (Q u) : Matrix (Fin 2) (Fin 2) ℤ) b ∈ X.B N l (2 * e - 1) :=
    fun u b hb => (sBStab Ω ε X l N (2 * e - 1) hNpos b hb).2.1 _ (mem u)
  have hΔ : ∀ u (b : X.Fn l), b ∈ X.B N l (2 * e - 1) →
      pr (X.act l (sgD N l (Q u) : Matrix (Fin 2) (Fin 2) ℤ) b) = δ (Q u) • pr b :=
    fun u b hb => hpr _ (hQp u) (hQd u) b hb
  have formula : ∀ (q : ℕ) (u : (ZMod N)ˣ), q.Prime → ¬ q ∣ l * N → (u : ZMod N) = q →
      ∀ b ∈ X.B N l (2 * e - 1), pr (X.diam N l q b) = δ (Q u) • pr b := by
    intro q u hq hd hu b hb
    have e1 : X.diam N l q b = X.act l (sgD N l (Q u) : Matrix (Fin 2) (Fin 2) ℤ) b := by
      rw [hdiam]
      exact dc_same X l N (2 * e - 1) _ _ (hisD q hq hd).1 (mem u)
        (by rw [(hisD q hq hd).2, en_u, hu]) b hb
    rw [e1]
    exact hΔ u b hb
  have mul : ∀ u v, δ (Q (u * v)) = δ (Q u) * δ (Q v) := by
    intro u v
    apply cancel
    have e2 : X.act l (((sgD N l (Q u) * sgD N l (Q v) : SL(2, ℤ))) : Matrix (Fin 2) (Fin 2) ℤ) b0 =
        X.act l (sgD N l (Q (u * v)) : Matrix (Fin 2) (Fin 2) ℤ) b0 :=
      dc_same X l N (2 * e - 1) _ _ (Subgroup.mul_mem _ (mem u) (mem v)) (mem (u * v))
        (by rw [dc_en N _ _ (mem u).1 (mem v).1, en_u, en_u, en_u, Units.val_mul]) b0 hb0
    rw [← hΔ (u * v) b0 hb0, ← e2, ← dc_mul X l, hΔ v _ (inB u b0 hb0), hΔ u b0 hb0, smul_smul, mul_comm]
  have one : δ (Q 1) = 1 := by
    apply cancel
    rw [one_smul, ← hΔ 1 b0 hb0]
    have e3 : X.act l (sgD N l (Q 1) : Matrix (Fin 2) (Fin 2) ℤ) b0 =
        X.act l ((1 : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) b0 :=
      dc_same X l N (2 * e - 1) _ _ (mem 1) (Subgroup.one_mem _) (by rw [en_u]; simp [en]) b0 hb0
    rw [e3, dc_fix X l N (2 * e - 1) 1 (Subgroup.one_mem _) b0 hb0]
  have inv : ∀ u : (ZMod N)ˣ, δ (Q u) * δ (Q u⁻¹) = 1 := fun u => by
    rw [← mul, mul_inv_cancel, one]
  refine ⟨MonoidHom.mk' (fun u => Units.mkOfMulEqOne (δ (Q u)) (δ (Q u⁻¹)) (inv u))
    (fun u v => by
      ext
      simp [mul]), ?_⟩
  intro q u hq hd hu b hb
  simp only [MonoidHom.mk'_apply, Units.val_mkOfMulEqOne]
  exact formula q u hq hd hu b hb
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.K4 GlobalTheory.KA UpperTheory.Kd.K4 UpperTheory.V.Z.Kato.Sym UpperTheory.V.Z.Kato.Nb
open scoped Matrix MatrixGroups Classical

theorem UpperTheory.V.Z.Kato.Nb.sRel0 :
    UpperTheory.V.Z.Kato.Nb.SRel0 := by
  intro l _ Ω _ _ _ ι e gN A W ε X pr N _ x c d gm ψ cf hA he c₀ Y hY r n
  obtain ⟨bB, hL, b, hb, hC⟩ := hY r n
  obtain ⟨-, -, -, -, hadd, -, -, heq, -⟩ := hA
  have hN : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have h2 : 2 * e + 1 - 2 = 2 * e - 1 := by omega
  rw [h2] at hL
  obtain ⟨-, -, -, -, -, -, -, hcy⟩ := sSlD Ω ε X N hN
  have hfix : ∀ (s : Ω ≃ₐ[ℚ] Ω) (y : (ZMod (topM l n r (N * N)))ˣ),
      (repM (topM l n r (N * N)) y)⁻¹ * s * repM (topM l n r (N * N)) (y * (cycM (topM l n r (N * N)) s)⁻¹) ∈
        fixMu Ω (topMu l n r N) := by
    intro s y
    have hm : ∀ s t : Ω ≃ₐ[ℚ] Ω, cycM (topM l n r (N * N)) (s * t) = cycM (topM l n r (N * N)) s * cycM (topM l n r (N * N)) t :=
      fun s t => (hcy (topM l n r (N * N)) s).2.1 t
    have hr := (hcy (topM l n r (N * N)) s).2.2.1
    refine (hcy (topM l n r (N * N)) _).2.2.2.1.2 ?_
    have h1 : y * cycM (topM l n r (N * N)) ((repM (topM l n r (N * N)) y)⁻¹ * s) = cycM (topM l n r (N * N)) s := by
      conv_lhs => rw [← hr y]
      rw [← hm, hr, mul_inv_cancel_left]
    rw [hm, hr, eq_inv_mul_of_mul_eq h1]
    simp [mul_comm, mul_left_comm]
  have hB := sBStab Ω ε X l N (2 * e - 1) hN
  obtain ⟨-, -, -, hsum, -, -, hgal, -⟩ := sApi Ω ε X l n
  let P : X.Fn l →+ (Fin 2 → Qbar l) := AddMonoidHom.mk' pr hadd
  refine ⟨GlobalTheory.KA.push (redM l n r (N * N)) (shB X l (topM l n r (N * N)) bB), b, fun s y => ⟨?_, ?_⟩, hb, fun s y => ?_⟩
  · exact Submodule.sum_mem _ fun y' _ => (hB _ (hL _ (hfix s y')).1).1 _
  · have h1 := hsum _ (Finset.univ.filter fun y' => redM l n r (N * N) y' = y) _ _
      (fun y' _ => hgal (repM (topM l n r (N * N)) y') _ (((l : ℤ_[l]) ^ c₀) • _) (hL _ (hfix s y')).2)
    have h3 : (∑ r₀, Y0 X l n r N x c d (2 * e - 1) (gm r₀) s y) =
        ∑ y' ∈ Finset.univ.filter (fun y' => redM l n r (N * N) y' = y),
          shB X l (topM l n r (N * N)) (clsBmu X l n r N x c d (2 * e + 1) gm) s y' := by

      simp only [Y0, GlobalTheory.KA.push, shB, clsBmu_eq, h2, map_sum]
      exact Finset.sum_comm
    simp only [map_smul, ← Finset.smul_sum] at h1
    beta_reduce
    rw [h3]
    exact h1
  · have h4 : pr (GlobalTheory.KA.push (redM l n r (N * N)) (shB X l (topM l n r (N * N)) bB) s y) = YfB X l pr W e ψ n r N bB s y := by
      refine (map_sum P _ _).trans (Finset.sum_congr rfl fun y' _ => ?_)
      exact heq _ _ (hL _ (hfix s y')).1
    rw [h4]
    exact hC s y
end
