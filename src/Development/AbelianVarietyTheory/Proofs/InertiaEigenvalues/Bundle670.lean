module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBreuilKisinModuleBasisOfFCrystal
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ConnPhiExtensionGeneratorEqZeta
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle642
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle625
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle626
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle622
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGaloisPrescribedUnramifiedKummer
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CupProductFiniteClassesCoboundary
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.WittVector.DiscreteValuationRing
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MemBallOfGaugeLt

@[expose] public section

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.CrysEpsFrob



theorem eps_frob_compat : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod O K l e a ι) (T : Lat a O K ϖ) (I : Ident t ϖ P T), letI := zlLat T; ∀ (E : FCrys l ↥(OL (ϖ.field a))) (jA : E.M (ainfObj (ϖ.field a)) →ₛₗ[(inclW l).comp (ainfId (ϖ.field a)).toRingHom] (WCb l ⊗[ℤ_[l]] ↥T.L.T)), Realises (ϖ.field a) E (ainfObj _) (ainfId _) ↥T.L.T (actZ T) jA → (∀ y : TW (OW l O) T, (∃ x : E.M (ϖ.prism a), y = kappa T (jA (E.tr (ϖ.toAinf a) x))) ↔ ∃ (m : Vec K a ι) (hm : m ∈ P.M), y = I.j (toW t ϖ P ⟨m, mem_ME_of_mem_M hm⟩)) → ∀ (oE : O → FHom E E), (∀ (c : O) (x : E.M (ainfObj (ϖ.field a))), jA ((oE c).u (ainfObj (ϖ.field a)) x) = (OfCrystal.mulZ T c).lTensor (WCb l) (jA x)) → ∀ (b : ι → E.M (ϖ.prism a)), (∀ j, ∃ hm : (bas j : Vec K a ι) ∈ P.M, kappa T (jA (E.tr (ϖ.toAinf a) (b j))) = I.j (toW t ϖ P ⟨bas j, mem_ME_of_mem_M hm⟩)) → ∀ (sh : K⟦X⟧ →+* K⟦X⟧⟦X⟧) (φ₂ : K⟦X⟧⟦X⟧ →+* K⟦X⟧⟦X⟧), (∀ (f : K⟦X⟧) (i : ℕ), (i.factorial : K⟦X⟧) * coeff i (sh f) = (PowerSeries.derivative (R := K))^[i] f) → (∀ f : K⟦X⟧, φ₂ (PowerSeries.C f) = PowerSeries.C (frob K l f)) → ∀ (PP : Obj l ↥(OL (ϖ.field a))) (p₀ p₁ : GlobalTheory.Prism.Hom (ϖ.prism a) PP) (κ : ZMod a → PP.A →+* K⟦X⟧⟦X⟧), PP.I = Ideal.span {(l : PP.A)} → (∀ τ (x : (Wq l a)⟦X⟧), κ τ (p₀.f x) = PowerSeries.C (toAc t K (frobS l a x) τ : K⟦X⟧) ∧ κ τ (p₁.f x) = sh (toAc t K (frobS l a x) τ : K⟦X⟧)) → (∀ τ y, κ τ (PP.D.φ y) = φ₂ (κ (τ - 1) y)) → ∀ (Q : Type) [Fintype Q] (c : ι → ι → Q → O) (y : ι → ι → Q → PP.A), (∀ j, E.tr p₁ (b j) = ∑ i, ∑ q, y i j q • (oE (c i j q)).u PP (E.tr p₀ (b i))) → ∀ τ, (Matrix.of fun i j => ∑ q, c i j q • κ τ (y i j q)) * ((P.mx (τ - 1)).map (frob K l)).map sh = ((P.mx (τ - 1)).map (frob K l)).map PowerSeries.C * (Matrix.of fun i j => ∑ q, c i j q • κ (τ - 1) (y i j q)).map φ₂ := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ t ϖ ι _ _ P T I
  intro EE jA hR him oE hoE b hb sh φ₂ hsh hφC PP p₀ p₁ κ hI hκ hκφ Q _ c y hy τ
  letI := zlLat T
  haveI hK : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ_[l] K).injective

  obtain ⟨J, hJ⟩ : ∃ J : EE.M (ϖ.prism a) →+ TW (OW l O) T,
      ∀ x, J x = kappa T (jA (EE.tr (ϖ.toAinf a) x)) :=
    ⟨(kappa T).comp (jA.toAddMonoidHom.comp (EE.tr (ϖ.toAinf a)).toAddMonoidHom), fun _ => rfl⟩
  have h1 : ∀ z : TW (OW l O) T, (∃ x, z = J x) ↔
      ∃ (m : Vec K a ι) (hm : m ∈ P.M), z = I.j (toW t ϖ P ⟨m, mem_ME_of_mem_M hm⟩) := fun z => by
    simp only [hJ]
    exact him z
  obtain ⟨cc, hcM, hcJ, hsurj⟩ := GlobalTheory.BKCoord.exists_coord I J h1
  have hJi : Function.Injective J := by
    have := EE.proj (ainfObj (ϖ.field a))
    have := EE.proj (ϖ.prism a)
    intro u v huv
    rw [hJ, hJ] at huv
    exact GlobalTheory.BKCoord.semiBC_injective (EE.tr_bc (ϖ.toAinf a)) (GlobalTheory.BKCoord.ev_injective ϖ)
      (GlobalTheory.BKCoord.semiBC_injective hR.bc inclW_injective ((kappa_bijective T).1 huv))
  have hinj : Function.Injective cc := fun x x' h => hJi (by rw [hcJ, hcJ]; simp only [h])
  have hw : ∀ (w : (ϖ.prism a).A) (x : EE.M (ϖ.prism a)),
      cc (w • x) = fun τ i => (toAc t K w τ : K⟦X⟧) * cc x τ i := by
    intro w x
    refine GlobalTheory.BKCoord.eq_of_j_eq_toAc I w ⟨_, mem_ME_of_mem_M (hcM x)⟩ ⟨_, mem_ME_of_mem_M (hcM _)⟩ ?_
    have h3 := congrArg jA ((EE.tr (ϖ.toAinf a)).map_smulₛₗ w x)
    have h4 := congrArg (kappa T) (h3.trans (jA.map_smulₛₗ _ _))
    have h5 := h4.trans (GlobalTheory.BKCoord.kappa_smul T _ _)
    rewrite [← hcJ, ← hcJ, hJ, hJ]
    exact h5
  have hU : ∀ (o : O) x, cc ((oE o).u (ϖ.prism a) x) =
      fun τ i => PowerSeries.C (algebraMap O K o) * cc x τ i := by
    intro o x
    refine GlobalTheory.BKCoord.eq_of_j_eq_const I o ⟨_, mem_ME_of_mem_M (hcM x)⟩ ⟨_, mem_ME_of_mem_M (hcM _)⟩ ?_
    have h3 := (congrArg jA ((oE o).u_tr (ϖ.toAinf a) x)).symm.trans (hoE o _)
    have h4 := (congrArg (kappa T) h3).trans (GlobalTheory.BKCoord.kappa_mulZ T o _)
    rewrite [← hcJ, ← hcJ, hJ, hJ]
    exact h4
  have hΦ : ∀ (x m : EE.M (ϖ.prism a)) (k : ℕ), IsFrac (A := (ϖ.prism a).A) (eis l a e)
      (EE.Φ (ϖ.prism a) ⟨eis l a e, Ideal.mem_span_singleton_self _⟩ x) m k →
      cc m = fun τ i => E K l e ^ k * P.phi (cc x) τ i := by
    intro x m k h
    refine GlobalTheory.BKCoord.eq_of_j_eq_phi I k (hcM x) ⟨_, mem_ME_of_mem_M (hcM _)⟩ ?_
    have h3 := (congrArg (kappa T) (GlobalTheory.BKCoord.j_frob hR x m k h)).trans (GlobalTheory.BKCoord.kappa_smul T _ _)
    have h4 := GlobalTheory.BKCoord.kappa_frob T (jA (EE.tr (ϖ.toAinf a) x))
    rewrite [← hcJ, ← hcJ, hJ, hJ]
    exact h3.trans (congrArg _ h4)
  have hcb : ∀ j, cc (b j) = bas j := by
    intro j
    obtain ⟨hm, hbj⟩ := hb j
    have h2 := (hcJ (b j)).symm.trans ((hJ (b j)).trans hbj)
    exact congrArg Subtype.val (toW_injective t ϖ P (I.j.injective h2))

  obtain ⟨lam₀, hl₀, ht₀⟩ := GlobalTheory.CrysExt.exists_coord l a e O K t ϖ ι EE cc hw PP p₀ κ PowerSeries.C
    (fun τ w => (hκ τ w).1)
  obtain ⟨lam₁, hl₁, ht₁⟩ := GlobalTheory.CrysExt.exists_coord l a e O K t ϖ ι EE cc hw PP p₁ κ sh
    (fun τ w => (hκ τ w).2)
  obtain ⟨ε', hε'⟩ := GlobalTheory.BKGal.CrysEps.exists_eps l a e O K t ϖ ι P EE cc hinj hcM hsurj hw
    (fun o => ⟨oE o, hU o⟩) sh hsh PP p₀ p₁ κ hκ lam₀ lam₁ hl₀ hl₁ ht₀ ht₁
  have hsh1 : ∀ f, PowerSeries.constantCoeff (sh f) = f := fun f => by simpa using hsh f 0
  have hshinj : Function.Injective sh := fun f g h => by rw [← hsh1 f, ← hsh1 g, h]
  have hl0 : (l : K) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero
  have hl1 : (l : K⟦X⟧) ≠ 0 := fun h => hl0 (by simpa using congrArg PowerSeries.constantCoeff h)
  have hl2 : (l : K⟦X⟧⟦X⟧) ≠ 0 := fun h => hl1 (by simpa using congrArg PowerSeries.constantCoeff h)
  have hE : E K l e ≠ 0 := fun h => hl0 (by
    simpa [E, NeZero.ne e] using congrArg PowerSeries.constantCoeff h)
  have hshE : sh (frob K l (E K l e)) ≠ 0 := by
    rw [map_ne_zero_iff _ hshinj, map_ne_zero_iff _ (frob_injective l)]; exact hE
  have hl : (l : PP.A) ∈ PP.I := hI ▸ Ideal.mem_span_singleton_self _
  have hfb : ∀ (j : ι) (σ : ZMod a) (i : ι), frob K l (bas j σ i) = bas j σ i := by
    intro j σ i
    rcases eq_or_ne i j with rfl | h
    · simp [bas]
    · simp [bas, Pi.single_eq_of_ne h]

  have hl1b : ∀ j σ, lam₁ (EE.tr p₁ (b j)) σ = Pi.single j 1 := by
    intro j σ; funext i
    rw [ht₁, hcb, hfb]
    rcases eq_or_ne i j with rfl | h
    · simp [bas]
    · simp [bas, Pi.single_eq_of_ne h]

  have hε'col : ∀ σ i j, ε' σ i j = lam₀ (EE.tr p₁ (b j)) σ i := by
    intro σ i j
    rw [hε' _ σ, hl1b, Matrix.mulVec_single_one]; rfl

  have hEps : ∀ σ i j, lam₀ (EE.tr p₁ (b j)) σ i = ∑ q, c i j q • κ σ (y i j q) := by
    intro σ i j
    have hU0 : ∀ (o : O) (i' : ι), lam₀ ((oE o).u PP (EE.tr p₀ (b i'))) σ i =
        if i = i' then PowerSeries.C (PowerSeries.C (algebraMap O K o)) else 0 := by
      intro o i'
      rw [(oE o).u_tr, ht₀, hU, hcb]
      rcases eq_or_ne i i' with rfl | h
      · simp [bas]
      · simp [bas, Pi.single_eq_of_ne h, h]

    rw [hy j, map_sum, Finset.sum_apply, Finset.sum_apply, Finset.sum_eq_single i]

    · rw [map_sum, Finset.sum_apply, Finset.sum_apply]
      refine Finset.sum_congr rfl fun q _ => ?_
      rw [hl₀, hU0, if_pos rfl, Algebra.smul_def, PowerSeries.algebraMap_apply,
        PowerSeries.algebraMap_apply, mul_comm]
    · intro i' _ h

      rw [map_sum, Finset.sum_apply, Finset.sum_apply]
      refine Finset.sum_eq_zero fun q _ => ?_
      rw [hl₀, hU0, if_neg (Ne.symm h), mul_zero]
    · intro h; exact absurd (Finset.mem_univ i) h
  refine Matrix.ext fun i j => ?_
  obtain ⟨n, k, hn⟩ := exists_isFrac (l : PP.A) (EE.Φ PP ⟨l, hl⟩ (EE.tr p₁ (b j)))

  have hA := GlobalTheory.CrysFrobCoord.frob_in_coordinates l a e O K t ϖ ι P EE cc hw hΦ PP hl p₀ κ
    PowerSeries.C φ₂ (fun τ w => (hκ τ w).1) hκφ hφC PowerSeries.C_injective lam₀ hl₀ ht₀ _ n k hn τ i

  obtain ⟨m', k', hm'⟩ := exists_isFrac (A := (ϖ.prism a).A) (eis l a e)
    (EE.Φ (ϖ.prism a) ⟨eis l a e, Ideal.mem_span_singleton_self _⟩ (b j))
  obtain ⟨r, hr⟩ := EE.Φ_nat p₁ ⟨eis l a e, Ideal.mem_span_singleton_self _⟩ ⟨l, hl⟩ (b j) m' k' n k hm' hn
  have hκE : κ τ (p₁.f (eis l a e)) = sh (frob K l (E K l e)) := by
    rw [(hκ τ _).2, ← GlobalTheory.CrysFrobCoord.frob_toAc, GlobalTheory.CrysFrobCoord.coe_toAc_eis]
  have hJl : κ τ (l : PP.A) = l := map_natCast _ _
  have hB : ∀ i', lam₁ n τ i' = (l : K⟦X⟧⟦X⟧) ^ k * sh (frob K l (P.mx (τ - 1) i' j)) := by
    intro i'
    have h1 := congrArg (fun z => lam₁ z τ i') hr
    simp only [hl₁, map_sub, Pi.sub_apply, map_zero, Pi.zero_apply, map_pow, map_mul, hJl, hκE] at h1
    have h2 := sub_eq_zero.1 ((mul_eq_zero.1 h1).resolve_left (pow_ne_zero _ (mul_ne_zero hshE hl2)))
    have hm'c : cc m' (τ - 1) i' = E K l e ^ k' * P.mx (τ - 1) i' j := by
      rw [hΦ _ _ _ hm', hcb]
      simp only [PhiMod.phi_apply]
      congr 1
      have : frobV l (bas j (τ - 1 - 1) : ι → K⟦X⟧) = Pi.single j 1 := funext fun i'' => by
        rw [frobV_apply, hfb]; rfl
      rw [this, Matrix.mulVec_single_one]; rfl
    rw [ht₁, hm'c, map_mul, map_mul, map_pow, map_pow] at h2
    refine mul_left_cancel₀ (pow_ne_zero k' hshE) ?_
    rw [← h2]; ring
  have hlk : ((l : K⟦X⟧⟦X⟧) ^ k) ≠ 0 := pow_ne_zero k hl2
  refine mul_left_cancel₀ hlk ?_
  have hC := congrFun (hε' n τ) i
  rw [hA] at hC
  simp only [Matrix.mulVec, dotProduct, hB, hε'col, hEps, Matrix.map_apply, Matrix.of_apply] at hC
  simp only [Matrix.mul_apply, Matrix.map_apply, Matrix.of_apply]
  rw [hC, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring

end GlobalTheory.CrysEpsFrob
end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix

noncomputable section

namespace GlobalTheory.RootLt

open Polynomial

theorem norm_iotaO_le_one (l : ℕ) [Fact l.Prime] (a : ℕ) [NeZero a] (w : Wq l a) :
    ‖GlobalTheory.TameFrob.iotaO l a w‖ ≤ 1 := by
  have hw : w ∈ Submodule.span ℤ_[l] (Set.range (WittVector.teichmuller l : Fq l a → Wq l a)) := by
    rw [span_teich]; trivial
  induction hw using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨z, rfl⟩ := hx
    set ω := GlobalTheory.TameFrob.iotaO l a (WittVector.teichmuller l z)
    have hω : ω ^ l ^ a = ω := by
      simp only [ω]
      rw [← map_pow, ← map_pow, Fq.pow_card]
    by_contra h
    push_neg at h
    have h2 : 1 < l ^ a := Nat.one_lt_pow (NeZero.ne a) (Fact.out : l.Prime).one_lt
    have h3 : ‖ω‖ ^ 1 < ‖ω‖ ^ l ^ a := pow_lt_pow_right₀ h h2
    rw [pow_one, ← norm_pow, hω] at h3
    exact lt_irrefl _ h3
  | zero => simp
  | add x y _ _ hx hy =>
    rw [map_add (f := _)]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hx hy)
  | smul c x _ hx =>
    rw [Algebra.smul_def, map_mul, GlobalTheory.TameFrob.iotaO_algebraMap, norm_mul]
    have hc : ‖algebraMap ℚ_[l] (Om l) (c : ℚ_[l])‖ ≤ 1 :=
      (PadicAlgCl.norm_extends l (c : ℚ_[l])).le.trans c.2
    calc _ ≤ 1 * 1 := mul_le_mul hc hx (norm_nonneg _) zero_le_one
      _ = 1 := one_mul 1

theorem norm_lt_one_of_isRoot : ∀ (l : ℕ) [Fact l.Prime] (a : ℕ) [NeZero a] (P : Polynomial (Wq l a)), P.Monic →
    (∀ i < P.natDegree, (l : Wq l a) ∣ P.coeff i) → ∀ x : Om l, (P.map (GlobalTheory.TameFrob.iotaO l a)).IsRoot x → ‖x‖ < 1 := by
  intro l _ a _ P hP hdiv x hx
  set d := P.natDegree with hd
  rcases Nat.eq_zero_or_pos d with h0 | hpos
  · have : P = 1 := Polynomial.eq_one_of_monic_natDegree_zero hP h0
    rw [this, Polynomial.map_one] at hx
    simp [Polynomial.IsRoot] at hx
  by_contra hge
  push_neg at hge
  have hlpos : (0 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).pos
  have hl1 : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt

  have hnl : ‖GlobalTheory.TameFrob.iotaO l a (l : Wq l a)‖ = (l : ℝ)⁻¹ := by
    rw [map_natCast, ← map_natCast (algebraMap ℚ_[l] (Om l)), PadicAlgCl.norm_extends, Padic.norm_p]
  have hcoef : ∀ i < d, ‖GlobalTheory.TameFrob.iotaO l a (P.coeff i)‖ ≤ (l : ℝ)⁻¹ := by
    intro i hi
    obtain ⟨c, hc⟩ := hdiv i hi
    rw [hc, map_mul, norm_mul, hnl]
    calc _ ≤ (l : ℝ)⁻¹ * 1 := mul_le_mul_of_nonneg_left (norm_iotaO_le_one l a c) (by positivity)
      _ = _ := mul_one _
  have hxd : (1 : ℝ) ≤ ‖x‖ ^ d := one_le_pow₀ hge

  have heq : x ^ d + ∑ i ∈ Finset.range d, GlobalTheory.TameFrob.iotaO l a (P.coeff i) * x ^ i = 0 := by
    have h := hx
    rw [Polynomial.IsRoot, hP.as_sum] at h

    simpa [Polynomial.eval_finsetSum, Polynomial.map_add (f := _), Polynomial.map_pow, Polynomial.map_sum,
    Polynomial.map_mul] using h
  have hsum : ‖∑ i ∈ Finset.range d, GlobalTheory.TameFrob.iotaO l a (P.coeff i) * x ^ i‖ ≤ (l : ℝ)⁻¹ * ‖x‖ ^ d := by
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) fun i hi => ?_
    have hi' := Finset.mem_range.1 hi
    rw [norm_mul, norm_pow]
    exact mul_le_mul (hcoef i hi') (pow_le_pow_right₀ hge hi'.le) (by positivity) (by positivity)
  have hxeq : x ^ d = -∑ i ∈ Finset.range d, GlobalTheory.TameFrob.iotaO l a (P.coeff i) * x ^ i :=
    eq_neg_of_add_eq_zero_left heq
  have h1 : ‖x‖ ^ d ≤ (l : ℝ)⁻¹ * ‖x‖ ^ d := by
    calc ‖x‖ ^ d = ‖x ^ d‖ := (norm_pow _ _).symm
      _ = ‖∑ i ∈ Finset.range d, GlobalTheory.TameFrob.iotaO l a (P.coeff i) * x ^ i‖ := by rw [hxeq, norm_neg]
      _ ≤ _ := hsum
  have h2 : (l : ℝ)⁻¹ * ‖x‖ ^ d < ‖x‖ ^ d := by
    have : (l : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hl1
    nlinarith
  exact lt_irrefl _ (h1.trans_lt h2)

end GlobalTheory.RootLt
end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix

noncomputable section

namespace GlobalTheory.TameFrob

open Polynomial

attribute [local instance] algK isFractionRing

theorem irreducible_map_iota_of_eisenstein : ∀ (l : ℕ) [Fact l.Prime] (a : ℕ) [NeZero a] (E : Polynomial (Wq l a)), E.Monic → 0 < E.natDegree →
    (∀ i < E.natDegree, (l : Wq l a) ∣ E.coeff i) → (∃ w : (Wq l a)ˣ, E.coeff 0 = (l : Wq l a) * w) →
    Irreducible (E.map (GlobalTheory.TameFrob.iota l a)) := by
  intro l _ a _ E hmon hdeg hdiv ⟨w, hw⟩
  have hP : (Ideal.span {(l : Wq l a)}).IsPrime := by
    rw [← WittVector.ker_constantCoeff]; exact RingHom.ker_isPrime _
  have hl0 : (l : Wq l a) ≠ 0 := fun h => by
    have := congrArg (iotaO l a) h
    rw [map_natCast, map_zero] at this
    exact (Fact.out : l.Prime).ne_zero (by exact_mod_cast this)
  have hW : Irreducible E := by
    refine Polynomial.IsEisensteinAt.irreducible ⟨?_, ?_, ?_⟩ hP hmon.isPrimitive hdeg
    · rw [hmon.leadingCoeff]
      exact fun h => hP.ne_top ((Ideal.eq_top_iff_one _).2 h)
    · intro n hn
      exact Ideal.mem_span_singleton.2 (hdiv n hn)
    · rw [hw, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
      rintro ⟨c, hc⟩
      have h1 : (l : Wq l a) * ((w : Wq l a) - l * c) = 0 := by linear_combination hc
      have h2 : (w : Wq l a) = l * c := by
        have := (mul_eq_zero.1 h1).resolve_left hl0
        linear_combination this
      have h3 := congrArg WittVector.constantCoeff h2
      rw [map_mul, map_natCast, CharP.cast_eq_zero, zero_mul] at h3
      exact (w.isUnit.map WittVector.constantCoeff).ne_zero h3
  have h := (hmon.irreducible_iff_irreducible_map_fraction_map (K := ↥(Kunr l a))).1 hW
  exact h

end GlobalTheory.TameFrob
end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix

namespace GlobalTheory.TameFrob

theorem exists_algEquiv_iotaO_sigma : ∀ (l : ℕ) [Fact l.Prime] (a : ℕ) [NeZero a], ∃ Φ : Om l ≃ₐ[ℚ_[l]] Om l,
    ∀ w : Wq l a, Φ (GlobalTheory.TameFrob.iotaO l a w) = GlobalTheory.TameFrob.iotaO l a (sigma l a w) := by
  intro l _ a _
  letI : Algebra (Wq l a) ↥(Kunr l a) := algK l a
  letI : IsFractionRing (Wq l a) ↥(Kunr l a) := by
    refine (isLocalization_iff (nonZeroDivisors (Wq l a)) ↥(Kunr l a)).2 ⟨?_, ?_, ?_⟩
    · intro s
      refine IsUnit.mk0 _ fun h => nonZeroDivisors.coe_ne_zero s (iota_injective l a ?_)
      rw [← algebraMap_K, h, map_zero]
    · intro y
      obtain ⟨w, s, hs, h⟩ := exists_frac l a y
      exact ⟨⟨w, ⟨s, mem_nonZeroDivisors_of_ne_zero hs⟩⟩, Subtype.ext (by simpa [algebraMap_K] using h)⟩
    · intro x y h
      exact ⟨1, by rw [iota_injective l a h]⟩
  let fr : ↥(Kunr l a) →+* Om l :=
    IsFractionRing.lift (g := (iotaO l a).comp (sigma l a).toRingEquiv.toRingHom)
      ((iotaO_injective l a).comp (sigma l a).injective)
  have hfr (w : Wq l a) : fr (iota l a w) = iotaO l a (sigma l a w) :=
    IsFractionRing.lift_algebraMap _ w
  let f : ↥(Kunr l a) →ₐ[ℚ_[l]] Om l := {
    toRingHom := fr
    commutes' := by
      intro r
      have h : fr.comp (algebraMap ℚ_[l] ↥(Kunr l a)) = algebraMap ℚ_[l] (Om l) := by
        refine IsLocalization.ringHom_ext (nonZeroDivisors ℤ_[l]) (RingHom.ext fun u => ?_)
        have h1 : algebraMap ℚ_[l] ↥(Kunr l a) (algebraMap ℤ_[l] ℚ_[l] u) =
            iota l a (algebraMap ℤ_[l] (Wq l a) u) :=
          Subtype.ext (by rw [coe_iota, iotaO_algebraMap]; rfl)
        simp only [RingHom.comp_apply]
        rw [h1, hfr, AlgEquiv.commutes, iotaO_algebraMap]
        rfl
      exact RingHom.congr_fun h r }
  let φ : Om l →ₐ[ℚ_[l]] Om l := f.liftNormal (Om l)
  refine ⟨AlgEquiv.ofBijective φ φ.normal_bijective, fun w => ?_⟩
  have h := AlgHom.liftNormal_commutes f (Om l) (iota l a w)
  rw [AlgEquiv.ofBijective_apply]
  exact h.trans (hfr w)

end GlobalTheory.TameFrob
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix

namespace GlobalTheory.ExpandCoeff

open Polynomial

theorem coeff_eq_zero_of_roots : ∀ (l : ℕ) [Fact l.Prime] (a : ℕ) [NeZero a] (E : Polynomial (Wq l a)), E.Monic →
    Irreducible (E.map (GlobalTheory.TameFrob.iota l a)) → ∀ z : Om l, z ≠ 0 →
    (∀ z' : Om l, Polynomial.aeval z' (minpoly (↥(Kunr l a)) z) = 0 → ∀ y : Om l, y ^ l = z' →
      (E.map (GlobalTheory.TameFrob.iotaO l a)).IsRoot y) →
    ∀ i, ¬ l ∣ i → E.coeff i = 0 := by
  intro l hl a _ E hE hirr z hz hroot i hi
  have hl0 : 0 < l := hl.out.pos
  set K := ↥(Kunr l a)
  have hzi : IsIntegral K z := Algebra.IsIntegral.isIntegral z
  set m := minpoly K z with hm
  set φ := algebraMap K (Om l)
  set EK := E.map (GlobalTheory.TameFrob.iota l a) with hEKdef
  set Q := E.map (GlobalTheory.TameFrob.iotaO l a) with hQdef
  have hcomp : φ.comp (GlobalTheory.TameFrob.iota l a) = GlobalTheory.TameFrob.iotaO l a := RingHom.ext fun w => rfl
  have hmapQ : EK.map φ = Q := by rw [hEKdef, Polynomial.map_map, hcomp]
  have hev : ∀ y : Om l, Polynomial.aeval y EK = Q.eval y := fun y => by
    rw [Polynomial.aeval_def, ← Polynomial.eval_map, hmapQ]
  obtain ⟨y0, hy0⟩ := IsAlgClosed.exists_pow_nat_eq z hl0
  have hQ0 : Q.IsRoot y0 := hroot z (minpoly.aeval K z) y0 hy0
  have hEK : EK.Monic := hE.map _
  have hEKmin : EK = minpoly K y0 := minpoly.eq_of_irreducible_of_monic hirr (by rw [hev]; exact hQ0) hEK
  set P := Polynomial.expand K l m with hPdef
  have hPmon : P.Monic := (minpoly.monic hzi).expand hl0
  have hPy0 : Polynomial.aeval y0 P = 0 := by
    rw [hPdef, Polynomial.expand_aeval, hy0, minpoly.aeval]
  have hdvd : EK ∣ P := hEKmin ▸ minpoly.dvd K y0 hPy0

  have hmsep : m.Separable := Algebra.IsSeparable.isSeparable K z
  have hc0 : m.coeff 0 ≠ 0 := minpoly.coeff_zero_ne_zero hzi hz
  have hPsep : P.Separable := by
    unfold Polynomial.Separable
    rw [Polynomial.derivative_expand]
    have h1 : IsCoprime P (Polynomial.expand K l (Polynomial.derivative m)) :=
      IsCoprime.map hmsep (Polynomial.expand K l).toRingHom
    have h2 : IsCoprime P (Polynomial.X ^ (l - 1)) := by
      refine IsCoprime.pow_right ?_
      refine IsCoprime.symm ((Polynomial.irreducible_X.coprime_iff_not_dvd).2 ?_)
      rw [Polynomial.X_dvd_iff, hPdef, Polynomial.coeff_expand hl0, if_pos (dvd_zero l), Nat.zero_div]
      exact hc0
    have h3 : IsCoprime P ((l : K[X])) := by
      have hu : IsUnit ((l : K[X])) := by
        rw [← Polynomial.C_eq_natCast]
        exact Polynomial.isUnit_C.2 (IsUnit.mk0 _ (Nat.cast_ne_zero.2 hl.out.ne_zero))
      exact ⟨0, ↑(hu.unit⁻¹), by rw [zero_mul, zero_add, IsUnit.val_inv_mul]⟩
    exact h1.mul_right (h3.mul_right h2)
  set P' := P.map φ with hP'def
  have hP'sep : P'.Separable := hPsep.map
  have hP'0 : P' ≠ 0 := (hPmon.map φ).ne_zero
  have hQne : Q ≠ 0 := (hE.map _).ne_zero
  have hnod : P'.roots.Nodup := Polynomial.nodup_roots hP'sep
  have hcard : Multiset.card P'.roots = P'.natDegree :=
    (Polynomial.splits_iff_card_roots).1 (IsAlgClosed.splits P')
  have hle : P'.roots ≤ Q.roots := by
    refine (Multiset.le_iff_subset hnod).2 fun y hy => ?_
    rw [Polynomial.mem_roots hP'0, Polynomial.IsRoot, hP'def, Polynomial.eval_map, ← Polynomial.aeval_def,
      hPdef, Polynomial.expand_aeval] at hy
    exact (Polynomial.mem_roots hQne).2 (hroot _ hy y rfl)
  have hdeg : P.natDegree ≤ EK.natDegree := by
    have e1 : P'.natDegree = P.natDegree := Polynomial.natDegree_map φ
    have e2 : EK.natDegree = Q.natDegree := by
      rw [hEKdef, hQdef, Polynomial.natDegree_map_eq_of_injective (GlobalTheory.TameFrob.iota_injective l a),
        Polynomial.natDegree_map_eq_of_injective (GlobalTheory.TameFrob.iotaO_injective l a)]
    rw [← e1, e2, ← hcard]
    exact (Multiset.card_le_card hle).trans (Polynomial.card_roots' Q)
  have hEq : P = EK := Polynomial.eq_of_monic_of_dvd_of_natDegree_le hEK hPmon hdvd hdeg
  have hci : GlobalTheory.TameFrob.iota l a (E.coeff i) = 0 := by
    rw [← Polynomial.coeff_map, ← hEKdef, ← hEq, hPdef, Polynomial.coeff_expand hl0, if_neg hi]
  exact GlobalTheory.TameFrob.iota_injective l a (hci.trans (map_zero _).symm)

end GlobalTheory.ExpandCoeff
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

theorem _root_.GlobalTheory.T.cup_product_finite_classes_coboundary : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ (A A' : GRep ↥(GK K) ℚ_[l] LL O) (m : A.V →ₗ[LL] A'.V →ₗ[LL] LL), IsDR (P.PD K) A.ρ → IsDual1 (P.PD K) A.ρ A'.ρ m → ∀ a ∈ finiteCocycles (P.PD K) A.ρ, ∀ b ∈ finiteCocycles (P.PD K) A'.ρ, CobL (P.PD K) (cupL A'.ρ m a b) := by
  first | exact @GlobalTheory.BKOrth.bk_orth | exact GlobalTheory.BKOrth.bk_orth | (intros; apply GlobalTheory.BKOrth.bk_orth <;> assumption)
end
