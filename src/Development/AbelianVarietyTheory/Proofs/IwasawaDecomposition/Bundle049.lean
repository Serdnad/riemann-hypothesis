module

public import Formalism.ConjugateSelfDual.Bundle001
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Formalism.LocalToGlobal.GaloisLevelStructure.DefsAut
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle016
public import Mathlib.LinearAlgebra.Matrix.IsDiag
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle027
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle044
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle046
public import ReciprocityTheory.NeutralLocalFields.Bundle001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot
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
public import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.Order.CompletePartialOrder
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
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Mathlib.FieldTheory.Finite.Basic
import ReciprocityTheory.GaloisValuations.GlobalA

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2

namespace GlobalTheory.TameTau

theorem exists_root_congr_unit : ∀ {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    [IsAlgClosure E Ω] (A : ValuationSubring Ω) (P : HeightOneSpectrum (𝓞 E)),
    IsPlaceOver A P → ∀ u : 𝓞 E, u ∉ P.asIdeal →
      ∃ ζ : Ω, ζ ^ (normV P - 1) = 1 ∧ A.valuation (ζ - algebraMap E Ω (u : E)) < 1 := by
  intro E Ω _ _ _ _ _ A P hA u hu
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E
  haveI hfin : Finite (𝓞 E ⧸ P.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ P.ne_bot
  letI : Fintype (𝓞 E ⧸ P.asIdeal) := Fintype.ofFinite _
  haveI : P.asIdeal.IsMaximal := P.isMaximal
  letI : Field (𝓞 E ⧸ P.asIdeal) := Ideal.Quotient.field _
  set q := normV P with hq
  have hqc : q = Fintype.card (𝓞 E ⧸ P.asIdeal) := by
    rw [hq, normV, Nat.card_eq_fintype_card]
  have hq1 : 1 < q := by rw [hqc]; exact Fintype.one_lt_card
  set n := q - 1 with hn
  have hn0 : 0 < n := by omega

  have hmem : u ^ n - 1 ∈ P.asIdeal := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_pow, map_one, sub_eq_zero]
    have h0 : (Ideal.Quotient.mk P.asIdeal u) ≠ 0 := by
      rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
    have := FiniteField.pow_card_sub_one_eq_one _ h0
    rwa [← hqc] at this
  have hlt : A.valuation (algebraMap E Ω ((u ^ n - 1 : 𝓞 E) : E)) < 1 := (hA _).mpr hmem
  set a : Ω := algebraMap E Ω (u : E) with ha
  have hcast : algebraMap E Ω ((u ^ n - 1 : 𝓞 E) : E) = a ^ n - 1 := by
    simp [ha]
  rw [hcast] at hlt

  set p : Polynomial Ω := Polynomial.X ^ n - Polynomial.C 1 with hp
  have hmon : p.Monic := Polynomial.monic_X_pow_sub_C 1 hn0.ne'
  have hprod := (IsAlgClosed.splits p).eq_prod_roots_of_monic hmon
  have heval : a ^ n - 1 = (p.roots.map (fun ζ => a - ζ)).prod := by
    have := congrArg (Polynomial.eval a) hprod
    rw [Polynomial.eval_multiset_prod, Multiset.map_map] at this
    simp only [hp, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
      Polynomial.eval_C, Function.comp_def] at this
    rw [this]
  by_contra hcon
  push_neg at hcon
  have hall : ∀ ζ ∈ p.roots, 1 ≤ A.valuation (a - ζ) := by
    intro ζ hζ
    have hroot : ζ ^ n = 1 := by
      have := (Polynomial.mem_roots hmon.ne_zero).mp hζ
      simpa [hp, sub_eq_zero] using this
    rw [Valuation.map_sub_swap]
    exact hcon ζ hroot
  have : 1 ≤ A.valuation (a ^ n - 1) := by
    rw [heval, map_multiset_prod, Multiset.map_map]
    have key : ∀ s : Multiset Ω, (∀ ζ ∈ s, 1 ≤ A.valuation (a - ζ)) →
        1 ≤ (s.map (A.valuation ∘ fun ζ => a - ζ)).prod := by
      intro s
      induction s using Multiset.induction_on with
      | empty => intro _; simp
      | cons b s ih =>
        intro h
        rw [Multiset.map_cons, Multiset.prod_cons]
        exact one_le_mul (h b (Multiset.mem_cons_self b s))
          (ih fun ζ hζ => h ζ (Multiset.mem_cons_of_mem hζ))
    exact key _ hall
  exact absurd hlt (not_lt.mpr this)

end GlobalTheory.TameTau
end

section

open Formalism.L2 Formalism.AUTREP ReciprocityTheory.Aut NumberField

namespace GlobalTheory.IsoFix

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {W : Type} [AddCommGroup W] [Module ℂ W]

theorem fixed_transport {ρ : Representation ℂ (GQ L n) W} {S S' : Submodule ℂ (GAf L n → W)} (K : Set (GAf L n))
    (hS : NG.IsSubrep ρ S) (hiso : NG.IsoRep S S') {x : GAf L n → W} (hx : x ∈ S') (hx0 : x ≠ 0)
    (hfix : ∀ κ ∈ K, NG.rt L n κ x = x) :
    ∃ f' ∈ S, f' ≠ 0 ∧ ∀ κ ∈ K, NG.rt L n κ f' = f' := by
  obtain ⟨T, hT⟩ := hiso
  have hTf0 : T (T.symm ⟨x, hx⟩) = ⟨x, hx⟩ := T.apply_symm_apply _
  refine ⟨(T.symm ⟨x, hx⟩ : S), (T.symm ⟨x, hx⟩).2, ?_, ?_⟩
  · intro h
    have h1 : T.symm ⟨x, hx⟩ = 0 := Subtype.ext h
    have h2 : (⟨x, hx⟩ : S') = 0 := by rw [← hTf0, h1, map_zero]
    exact hx0 (congrArg Subtype.val h2)
  · intro κ hκ
    have hmem : NG.rt L n κ ((T.symm ⟨x, hx⟩ : S) : GAf L n → W) ∈ S := hS.stable κ _ (T.symm ⟨x, hx⟩).2
    have key := hT κ (T.symm ⟨x, hx⟩) ⟨_, hmem⟩ rfl
    rw [hTf0] at key
    have h3 : T ⟨_, hmem⟩ = T (T.symm ⟨x, hx⟩) := by
      apply Subtype.ext
      rw [key, hTf0]
      exact hfix κ hκ
    exact congrArg Subtype.val (T.injective h3)

theorem iSup_finset_stable (s : Finset (Submodule ℂ (GAf L n → W)))
    (hs : ∀ i ∈ s, ∀ h, ∀ f ∈ i, NG.rt L n h f ∈ i) (h : GAf L n) :
    ∀ f ∈ (⨆ i ∈ s, i), NG.rt L n h f ∈ (⨆ i ∈ s, i) := by
  have hle : (⨆ i ∈ s, i) ≤ (⨆ i ∈ s, i).comap (NG.rt L n h) := by
    refine iSup₂_le fun i hi => ?_
    intro f hf
    exact (le_iSup₂ (f := fun i (_ : i ∈ s) => i) i hi) (hs i hi h f hf)
  exact fun f hf => hle hf

theorem fixed_of_mem_finset_sum (ρ : Representation ℂ (GQ L n) W) (S : Submodule ℂ (GAf L n → W))
    (K : Set (GAf L n)) (hS : NG.IsIrrRep ρ S) (s : Finset (Submodule ℂ (GAf L n → W))) :
    (↑s ⊆ {S' | NG.IsIrrRep ρ S' ∧ NG.IsoRep S S'}) → ∀ f ∈ (⨆ i ∈ s, i), f ≠ 0 →
      (∀ κ ∈ K, NG.rt L n κ f = f) → ∃ f' ∈ S, f' ≠ 0 ∧ ∀ κ ∈ K, NG.rt L n κ f' = f' := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro _ f hf hf0 _
    simp at hf
    exact absurd hf hf0
  | insert a s ha ih =>
    intro hsub f hf hf0 hfix
    have haF : NG.IsIrrRep ρ a ∧ NG.IsoRep S a := hsub (Finset.mem_insert_self a s)
    have hsF : (↑s : Set _) ⊆ {S' | NG.IsIrrRep ρ S' ∧ NG.IsoRep S S'} :=
      fun x hx => hsub (Finset.mem_insert_of_mem hx)
    rw [Finset.iSup_insert] at hf
    have hMst : ∀ h, ∀ g ∈ (⨆ i ∈ s, i), NG.rt L n h g ∈ (⨆ i ∈ s, i) :=
      iSup_finset_stable s (fun i hi => (hsF hi).1.1.stable)
    have hsubrep : NG.IsSubrep ρ (a ⊓ ⨆ i ∈ s, i) :=
      ⟨inf_le_left.trans haF.1.1.le, fun h g hg => ⟨haF.1.1.stable h g hg.1, hMst h g hg.2⟩⟩
    rcases haF.1.2.2 _ hsubrep inf_le_left with h0 | htop
    · obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hf
      have hyfix : ∀ κ ∈ K, NG.rt L n κ y = y := by
        intro κ hκ
        have e := hfix κ hκ
        rw [map_add (f := _)] at e
        have hd : NG.rt L n κ y - y ∈ a ⊓ ⨆ i ∈ s, i := by
          refine ⟨Submodule.sub_mem _ (haF.1.1.stable κ y hy) hy, ?_⟩
          have h4 : NG.rt L n κ y - y = z - NG.rt L n κ z := by
            rw [sub_eq_sub_iff_add_eq_add, e]
            exact add_comm _ _
          rw [h4]
          exact Submodule.sub_mem _ hz (hMst κ z hz)
        rw [h0, Submodule.mem_bot, sub_eq_zero] at hd
        exact hd
      by_cases hy0 : y = 0
      · subst hy0
        simp only [zero_add] at hf0 hfix
        exact ih hsF z hz hf0 hfix
      · exact fixed_transport K hS.1 haF.2 hy hy0 hyfix
    · have hle : a ≤ ⨆ i ∈ s, i := inf_eq_left.1 htop
      exact ih hsF f ((sup_le hle le_rfl) hf) hf0 hfix

theorem fixed_of_isoTyp : ∀ {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {W : Type} [AddCommGroup W]
    [Module ℂ W] (ρ : Representation ℂ (GQ L n) W) (S : Submodule ℂ (GAf L n → W)) (K : Set (GAf L n)),
    NG.IsIrrRep ρ S → ∀ f ∈ NG.isoTyp ρ S, f ≠ 0 → (∀ κ ∈ K, NG.rt L n κ f = f) →
      ∃ f' ∈ S, f' ≠ 0 ∧ ∀ κ ∈ K, NG.rt L n κ f' = f' := by
  intro L _ _ _ n W _ _ ρ S K hS f hf hf0 hfix
  obtain ⟨s, hs, hfs⟩ := Submodule.mem_sSup_iff_exists_finset.1 hf
  exact fixed_of_mem_finset_sum ρ S K hS s hs f hfs hf0 hfix

end GlobalTheory.IsoFix
end

section

open NumberField IsDedekindDomain ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2

namespace GlobalTheory

theorem principalCong_inv_mul :
    ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n N : ℕ) (x y : GAf L n),
    NG.Cong L n N x → NG.Cong L n N y → NG.Cong L n N (x⁻¹ * y) := by
  intro L _ _ _ n N x y hx hy
  have hxi : x⁻¹ ∈ Umax L n := (Umax L n).inv_mem hx.1
  refine ⟨(Umax L n).mul_mem hxi hy.1, fun i j => ?_⟩
  choose A hA eA using hx.2
  choose B hB eB using hy.2
  have hint : ∀ i j, ((x⁻¹).1 : Matrix (Fin n) (Fin n) (AL L)) i j ∈ ALint L := hxi
  have key : ((x⁻¹ * y).1 : Matrix (Fin n) (Fin n) (AL L)) - 1 =
      ((x⁻¹).1 : Matrix (Fin n) (Fin n) (AL L)) *
        (((y.1 : Matrix (Fin n) (Fin n) (AL L)) - 1) - ((x.1 : Matrix (Fin n) (Fin n) (AL L)) - 1)) := by
    have h1 : ((x⁻¹).1 : Matrix (Fin n) (Fin n) (AL L)) * (x.1 : Matrix (Fin n) (Fin n) (AL L)) = 1 := by
      rw [← Units.val_mul, ← Subgroup.coe_mul, inv_mul_cancel]; rfl
    rw [sub_sub_sub_cancel_right, mul_sub, h1, Subgroup.coe_mul, Units.val_mul]
  refine ⟨∑ k, ((x⁻¹).1 : Matrix (Fin n) (Fin n) (AL L)) i k * (B k j - A k j),
    Subring.sum_mem _ fun k _ => Subring.mul_mem _ (hint i k) (Subring.sub_mem _ (hB k j) (hA k j)), ?_⟩
  rw [← Matrix.sub_apply, key, Matrix.mul_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Matrix.sub_apply, Matrix.sub_apply, Matrix.sub_apply, eA, eB]
  ring

end GlobalTheory
end

section

open NumberField IsDedekindDomain ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2

noncomputable section

namespace GlobalTheory.CongSplit

theorem conj_entry {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} (x : GA L n) (i j : Fin n) :
    conjAL L ((x.1 : Matrix (Fin n) (Fin n) (AL L)) i j) =
      (((x⁻¹ : GA L n).1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) j i := by
  have hm := x.2
  simp only [GA, UGroup, Subgroup.mem_mk] at hm
  have h1 : ((x.1⁻¹ : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) = conjT (conjAL L) x.1 :=
    Units.inv_eq_of_mul_eq_one_right hm
  simp only [InvMemClass.coe_inv, h1, conjT, Matrix.transpose_apply, Matrix.map_apply]

theorem cong_of_loc : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (s : SplitPlace L) (N : ℕ), 0 < N →
    ∀ x : GAf L n, TrivOutside {s.v} x →
    (∀ i j, Valued.v (((s.loc n x : GL (Fin n) (s.v.adicCompletion (NumberField.maximalRealSubfield L))) :
        Matrix (Fin n) (Fin n) (s.v.adicCompletion (NumberField.maximalRealSubfield L))) i j -
        (1 : Matrix (Fin n) (Fin n) (s.v.adicCompletion (NumberField.maximalRealSubfield L))) i j) ≤
      Valued.v ((N : s.v.adicCompletion (NumberField.maximalRealSubfield L)))) →
    (∀ i j, Valued.v (((s.loc n x⁻¹ : GL (Fin n) (s.v.adicCompletion (NumberField.maximalRealSubfield L))) :
        Matrix (Fin n) (Fin n) (s.v.adicCompletion (NumberField.maximalRealSubfield L))) i j -
        (1 : Matrix (Fin n) (Fin n) (s.v.adicCompletion (NumberField.maximalRealSubfield L))) i j) ≤
      Valued.v ((N : s.v.adicCompletion (NumberField.maximalRealSubfield L)))) →
    NG.Cong L n N x := by
  intro L _ _ _ n s N hN x hx h1 h2
  obtain ⟨e, he, he'⟩ := GlobalTheory.SplitSep.exists_sep L s
  have hNL : (N : L) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  obtain ⟨u, hu⟩ : ∃ u : AL L, (N : AL L) * u = 1 := ⟨algebraMap L (AL L) (N : L)⁻¹, by
    rw [← map_natCast (algebraMap L (AL L)), ← map_mul, mul_inv_cancel₀ hNL, map_one]⟩
  have key : ∀ (f : AL L →+* s.v.adicCompletion (maximalRealSubfield L)) (z : AL L),
      Valued.v (f z) ≤ Valued.v ((N : s.v.adicCompletion (maximalRealSubfield L))) → Valued.v (f (u * z)) ≤ 1 := by
    intro f z hz
    have h := congrArg (fun t => Valued.v (f t)) hu
    simp only [map_mul, map_natCast, map_one] at h
    rw [map_mul, map_mul, ← h, mul_comm]
    exact mul_le_mul_left hz _
  suffices H : ∀ i j : Fin n, ∃ y ∈ ALint L, (x.1 : Matrix (Fin n) (Fin n) (AL L)) i j -
      (1 : Matrix (Fin n) (Fin n) (AL L)) i j = (N : AL L) * y by
    refine ⟨fun i j => ?_, H⟩
    obtain ⟨y, hy, hxy⟩ := H i j
    rw [sub_eq_iff_eq_add.1 hxy]
    refine add_mem (mul_mem (natCast_mem _ N) hy) ?_
    by_cases hij : i = j <;> simp [Matrix.one_apply, hij, Subring.one_mem, Subring.zero_mem]
  intro i j
  refine ⟨u * ((x.1 : Matrix (Fin n) (Fin n) (AL L)) i j - (1 : Matrix (Fin n) (Fin n) (AL L)) i j), ?_, ?_⟩
  · apply GlobalTheory.mem_ALint_of_supported_at_split L s e he he'
    · intro w hw
      have := congrFun (congrFun (hx w (by simpa using hw)) i) j
      simp only [Matrix.map_apply] at this
      rw [map_mul, map_sub, this]
      by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
    · apply key
      have e1 : s.proj ((x.1 : Matrix (Fin n) (Fin n) (AL L)) i j) =
          ((s.loc n x : GL (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) : Matrix (Fin n) (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) i j := rfl
      have e2 : s.proj ((1 : Matrix (Fin n) (Fin n) (AL L)) i j) =
          (1 : Matrix (Fin n) (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) i j := by
        by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
      rw [map_sub, e1, e2]
      exact h1 i j
    · apply key (s.proj.comp (conjAL L))
      have e1 : s.proj ((((x⁻¹ : GA L n).1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) j i) =
          ((s.loc n x⁻¹ : GL (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) : Matrix (Fin n) (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) j i := rfl
      have e2 : (s.proj.comp (conjAL L)) ((1 : Matrix (Fin n) (Fin n) (AL L)) i j) =
          (1 : Matrix (Fin n) (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) j i := by
        by_cases hij : i = j
        · simp [Matrix.one_apply, hij]
        · simp [Matrix.one_apply, hij, Ne.symm hij]
      rw [map_sub, e2, RingHom.comp_apply, conj_entry, e1]
      exact h2 j i
  · rw [← mul_assoc, hu, one_mul]

end GlobalTheory.CongSplit
end
end

section

noncomputable section

open NumberField Formalism.L2.NG ReciprocityTheory.Aut Formalism.AUTREP Matrix

namespace GlobalTheory.AlgWtHW

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

def upt (X : (L →+* ℂ) → Matrix (Fin n) (Fin n) ℂ) : (L →+* ℂ) × Fin n × Fin n → ℂ :=
  fun p => X p.1 p.2.1 p.2.2

def IsUPt (X : (L →+* ℂ) → Matrix (Fin n) (Fin n) ℂ) : Prop :=
  ∀ σ, X σ * (X (ComplexEmbedding.conjugate σ))ᵀ = 1

def ratPt (γ₀ : Matrix (Fin n) (Fin n) L) : (L →+* ℂ) → Matrix (Fin n) (Fin n) ℂ :=
  fun σ => γ₀.map σ

def evM {ι : Type} (P : ι → ι → MvPolynomial ((L →+* ℂ) × Fin n × Fin n) ℂ)
    (x : (L →+* ℂ) × Fin n × Fin n → ℂ) : Matrix ι ι ℂ :=
  Matrix.of fun i j => MvPolynomial.eval x (P i j)

def Agrees (a : AlgWt L n) {ι : Type} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℂ a.W)
    (P : ι → ι → MvPolynomial ((L →+* ℂ) × Fin n × Fin n) ℂ) : Prop :=
  ∀ (γ : GQ L n) (γ₀ : GL (Fin n) L),
    (((γ : GAf L n) : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) =
      (γ₀ : Matrix (Fin n) (Fin n) L).map (Algebra.TensorProduct.includeLeftRingHom) →
    LinearMap.toMatrix b b (a.ρ γ) =
      fun i j => MvPolynomial.eval (fun p => p.1 ((γ₀ : Matrix _ _ L) p.2.1 p.2.2)) (P i j)

structure IsPolyRep {ι : Type} [Fintype ι] [DecidableEq ι] (Φ : GL (Fin n) ℂ → Matrix ι ι ℂ) : Prop where
  one : Φ 1 = 1
  mul : ∀ A B, Φ (A * B) = Φ A * Φ B
  poly : ∀ i j, ∃ Q : MvPolynomial ((Fin n × Fin n) ⊕ (Fin n × Fin n)) ℂ, ∀ B : GL (Fin n) ℂ,
    Φ B i j = MvPolynomial.eval (Sum.elim (fun p => B.val p.1 p.2) (fun p => (B⁻¹).val p.1 p.2)) Q

def IsBEig {ι : Type} [Fintype ι] (Φ : GL (Fin n) ℂ → Matrix ι ι ℂ) (v : ι → ℂ) (lam : Fin n → ℤ) : Prop :=
  v ≠ 0 ∧ ∀ B : GL (Fin n) ℂ, B.val.BlockTriangular id → Φ B *ᵥ v = (∏ i, (B.val i i) ^ (lam i)) • v

def IsWtVec {ι : Type} [Fintype ι] (Φ : GL (Fin n) ℂ → Matrix ι ι ℂ) (μ : Fin n → ℤ) (w : ι → ℂ) : Prop :=
  ∀ D : GL (Fin n) ℂ, D.val.IsDiag → Φ D *ᵥ w = (∏ i, (D.val i i) ^ (μ i)) • w

def IsWt {ι : Type} [Fintype ι] (Φ : GL (Fin n) ℂ → Matrix ι ι ℂ) (μ : Fin n → ℤ) : Prop :=
  ∃ w : ι → ℂ, w ≠ 0 ∧ IsWtVec Φ μ w

def DomLE (μ lam : Fin n → ℤ) : Prop :=
  ∑ i, μ i = ∑ i, lam i ∧ ∀ k : ℕ, ∑ i ∈ Finset.univ.filter (fun i : Fin n => (i : ℕ) < k), μ i ≤
    ∑ i ∈ Finset.univ.filter (fun i : Fin n => (i : ℕ) < k), lam i

def Sle {ι : Type} [Fintype ι] (Φ : GL (Fin n) ℂ → Matrix ι ι ℂ) (lam : Fin n → ℤ) : Submodule ℂ (ι → ℂ) :=
  Submodule.span ℂ {w | ∃ ν, DomLE ν lam ∧ IsWtVec Φ ν w}

end GlobalTheory.AlgWtHW
end
end

section

open Metric Filter Topology Set

namespace GlobalTheory

theorem riemann_extension_coordinate_hyperplane : ∀ (n : ℕ) (U : Set (Fin n → ℂ)) (k : Fin n) (f : (Fin n → ℂ) → ℂ), IsOpen U → DifferentiableOn ℂ f {z | z ∈ U ∧ z k ≠ 0} → (∀ z₀ ∈ U, ∃ V ∈ nhds z₀, ∃ M : ℝ, ∀ z ∈ V, z ∈ U → z k ≠ 0 → ‖f z‖ ≤ M) → ∃ F : (Fin n → ℂ) → ℂ, DifferentiableOn ℂ F U ∧ ∀ z ∈ U, z k ≠ 0 → F z = f z := by
  intro n U k f hU hd hb
  refine ⟨fun z => if z k = 0 then limUnder (𝓝[≠] (0 : ℂ)) (fun t => f (Function.update z k t)) else f z,
    ?_, fun z _ hz => by simp [hz]⟩
  have hO : IsOpen {z : Fin n → ℂ | z ∈ U ∧ z k ≠ 0} :=
    hU.inter (isOpen_ne_fun (continuous_apply k) continuous_const)
  intro z₀ hz₀
  refine DifferentiableAt.differentiableWithinAt ?_
  by_cases h0 : z₀ k = 0
  · obtain ⟨V, hV, M, hM⟩ := hb z₀ hz₀
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (inter_mem (hU.mem_nhds hz₀) hV)
    have hr : 0 < ε / 3 := by positivity
    have h2 : ball z₀ (2 * (ε / 3)) ⊆ U ∩ V := (ball_subset_ball (by linarith)).trans hball
    have hG := ((GlobalTheory.T.differentiableAt_coordinate_cauchy_integral n U k f z₀ (ε / 3) hr h0 hU
      ((closedBall_subset_ball (by linarith)).trans (hball.trans inter_subset_left)) hd).const_smul
      ((2 * (Real.pi : ℂ) * Complex.I)⁻¹))
    refine hG.congr_of_eventuallyEq ?_
    filter_upwards [isOpen_ball.mem_nhds (mem_ball_self hr)] with z hz
    exact (GlobalTheory.T.cauchy_slice_eq_removable_extension n U k f z₀ (ε / 3) M hr h0 hU (h2.trans inter_subset_left) hd
      (fun z hz hzk => hM z (h2 hz).2 (h2 hz).1 hzk) z hz).symm
  · have hf : DifferentiableAt ℂ f z₀ := hd.differentiableAt (hO.mem_nhds ⟨hz₀, h0⟩)
    refine hf.congr_of_eventuallyEq ?_
    filter_upwards [hO.mem_nhds ⟨hz₀, h0⟩] with z hz
    simp [hz.2]
end GlobalTheory
end

section

open IsLocalRing

theorem _root_.GlobalTheory.T.isRegularLocalRing_adicCompletion' : ∀ (T : Type) [CommRing T] [IsRegularLocalRing T], IsRegularLocalRing (AdicCompletion (maximalIdeal T) T) := by
  first | exact @GlobalTheory.RegularCompletion.isRegularLocalRing_adicCompletion | exact GlobalTheory.RegularCompletion.isRegularLocalRing_adicCompletion | (intros; apply GlobalTheory.RegularCompletion.isRegularLocalRing_adicCompletion <;> assumption)
end

section

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host GlobalTheory.HeckeGal

namespace GlobalTheory.NormCompat

def locUnit (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) : Fˣ →* Ideles F :=
  (localIdele F v).comp (Units.map (algebraMap F (v.adicCompletion F)).toMonoidHom)

theorem locUnit_apply (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (a : Fˣ) :
    locUnit F v a = localIdele F v (Units.map (algebraMap F (v.adicCompletion F)).toMonoidHom a) := rfl

end GlobalTheory.NormCompat
end
end

section

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

open MonoidalCategory CartesianMonoidalCategory MonObj

namespace GlobalTheory.ModuliGenus

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem exists_eq_nsmul_of_dvd (D : Datum H) {n : ℕ} (hn : 0 < n) (a : D.La) (h : ∀ b, (n : ℤ) ∣ D.EF a b) :
    ∃ e, a = n • e := by
  choose c hc using h
  have hn' : (n : ℤ) ≠ 0 := by exact_mod_cast hn.ne'
  let ψ : D.La →+ ℤ := AddMonoidHom.mk' c fun x y => mul_left_cancel₀ hn' (by rw [mul_add, ← hc, ← hc, ← hc, map_add (f := _)])
  obtain ⟨e, he⟩ := D.unimod.2 ψ.toIntLinearMap
  refine ⟨e, D.unimod.1 (LinearMap.ext fun b => ?_)⟩
  rw [map_nsmul, he, hc, LinearMap.smul_apply, nsmul_eq_mul]
  rfl

variable {l : Level H} {B : Type} [CommRing B] {b : Base l B} {S : Scheme.{0}} {s : S ⟶ Sp B}

end GlobalTheory.ModuliGenus
end
end
