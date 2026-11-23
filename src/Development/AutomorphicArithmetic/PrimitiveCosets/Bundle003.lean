module

public import Development.AutomorphicArithmetic.PrimitiveCosets.CoreAtH
public import Development.AutomorphicArithmetic.PrimitiveCosets.ToEBij
public import Formalism.SizeWindowBrackets.ChainSlopeWindows.GaloisMapComplexConjugation
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.Window
public import Development.AutomorphicArithmetic.DedekindLFunctions.LandauTheorems.ZeroFreeOfRpowWindow
public import Development.AutomorphicArithmetic.PrimitiveCosets.Bundle001
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Basify
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AutomorphicArithmetic.DedekindLFunctions.CharFamily
import Development.AutomorphicArithmetic.DedekindLFunctions.SplitInertia
import Development.AutomorphicArithmetic.PrimitiveCosets.RecH
import Formalism.SizeWindowBrackets.ErrorFormsWeakWindowsFalse
import Formalism.SizeWindowBrackets.Bundle002
import Formalism.SizeWindowBrackets.QuotientSlopeBoundsWith
import Formalism.SizeWindowBrackets.SChain

@[expose] public section

section

open UpperTheory.Comparison₂ Deduction.CH Formalism Formalism.HC Formalism.D5 Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.ThickSetMeanBounds Formalism.LFunctionChainParameters.LErr
  Formalism.LFunctionChainParameters.LChain Formalism.LFunctionChainParameters.LHost

private theorem chr_val (φ : Frame) (ψ : AddChar (E0 × φ.A) ℂ) (g : φ.GG) :
    ((chr φ ψ g : ℂˣ) : ℂ) = ψ (Multiplicative.toAdd (toE φ g)) := rfl

private theorem sgn_val (s : ℤˣ) :
    (if Multiplicative.toAdd (LFunctionChainParameters.LHost.sgn2 s) = 0 then (1 : ℂ) else -1) = ((s : ℤ) : ℂ) := by
  rcases Int.units_eq_one_or s with rfl | rfl
  · have h0 : Multiplicative.toAdd (LFunctionChainParameters.LHost.sgn2 1) = 0 := by
      rw [map_one, toAdd_one]
    rw [if_pos h0]
    simp
  · have h1 : Multiplicative.toAdd (LFunctionChainParameters.LHost.sgn2 (-1)) = 1 := by decide
    rw [h1, if_neg (by decide)]
    simp

theorem UpperTheory.Comparison₂.chr_bij :
    ∀ φ : Frame, Function.Bijective (chr φ) ∧ chr φ 0 = 1 ∧ chr φ chC = φ.chC ∧ chr φ psC = φ.psC ∧
      (∀ ψ g, ((chr φ ψ g : ℂˣ) : ℂ) = ψ (Multiplicative.toAdd (toE φ g))) ∧
      (∀ ψ, ψ ∈ PsiA φ.A0 ↔ Frame.TrivialOnFirstFactor (chr φ ψ)) ∧ ∀ ψ, chr φ ψ ∈ φ.Xp ↔ (ψ ∈ PsiA φ.A0 ∧ ψ sgc0 = 1) := by
  intro φ
  obtain ⟨hbij, hiod, -, htau, -⟩ := toE_bij φ
  have trivA : ∀ ψ, ψ ∈ PsiA φ.A0 ↔ Frame.TrivialOnFirstFactor (chr φ ψ) := by
    intro ψ
    have key : ∀ s : φ.A, ((chr φ ψ (φ.tau1 s) : ℂˣ) : ℂ) = ψ ((0 : E0), s) := by
      intro s
      rw [chr_val, htau]
      rfl
    simp only [PsiA, Frame.TrivialOnFirstFactor, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h s hs
      apply Units.ext
      rw [Units.val_one, key]
      exact h s hs
    · intro h s hs
      have h2 := congrArg Units.val (h s hs)
      rw [key, Units.val_one] at h2
      exact h2
  let e := MulEquiv.ofBijective (toE φ) hbij
  have he : ∀ g, e g = toE φ g := fun g => rfl
  refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_, chr_val φ, trivA, ?_⟩
  · intro ψ ψ' h
    apply AddChar.ext
    intro a
    obtain ⟨g, hg⟩ := hbij.2 (Multiplicative.ofAdd a)
    have h2 := congrArg (fun θ : φ.Char => ((θ g : ℂˣ) : ℂ)) h
    simp only [chr_val, hg, toAdd_ofAdd] at h2
    exact h2
  · intro θ
    let ψ : AddChar (E0 × φ.A) ℂ :=
      { toFun := fun a => ((θ (e.symm (Multiplicative.ofAdd a)) : ℂˣ) : ℂ)
        map_zero_eq_one' := by
          simp only [ofAdd_zero, map_one, Units.val_one]
        map_add_eq_mul' := by
          intro a b
          simp only [ofAdd_add, map_mul, Units.val_mul] }
    refine ⟨ψ, ?_⟩
    refine MonoidHom.ext fun g => Units.ext ?_
    rw [chr_val]
    show ((θ (e.symm (Multiplicative.ofAdd (Multiplicative.toAdd (toE φ g)))) : ℂˣ) : ℂ) = _
    rw [ofAdd_toAdd, ← he, MulEquiv.symm_apply_apply]
  · refine MonoidHom.ext fun g => Units.ext ?_
    rw [chr_val, MonoidHom.one_apply, Units.val_one, AddChar.zero_apply]
  · refine MonoidHom.ext fun g => Units.ext ?_
    rw [chr_val]
    show (if Multiplicative.toAdd (LFunctionChainParameters.LHost.sgn2 g.1.2) = 0 then (1 : ℂ) else -1) = _
    rw [sgn_val]
    simp [Frame.chC, Frame.chD]
  · refine MonoidHom.ext fun g => Units.ext ?_
    rw [chr_val]
    show (if Multiplicative.toAdd (LFunctionChainParameters.LHost.sgn2 g.1.1) = 0 then (1 : ℂ) else -1) = _
    rw [sgn_val]
    simp [Frame.psC, Frame.chQ]
  · intro ψ
    have hv : ((chr φ ψ φ.iod : ℂˣ) : ℂ) = ψ sgc0 := by
      rw [chr_val, hiod]
      rfl
    simp only [Frame.Xp, Set.mem_setOf_eq]
    rw [← trivA]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨h1, ?_⟩
      rw [← hv, h2, Units.val_one]
    · rintro ⟨h1, h2⟩
      refine ⟨h1, Units.ext ?_⟩
      rw [hv, h2, Units.val_one]
end

section

open UpperTheory.Comparison₂ Deduction.CH Formalism Formalism.HC Formalism.D5 Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.ThickSetMeanBounds Formalism.LFunctionChainParameters.LErr
  Formalism.LFunctionChainParameters.LChain Formalism.LFunctionChainParameters.LHost

private theorem UpperTheory.Comparison₂.prim_read_dir (φ : Frame) (H : HostRaw φ) (ψ : AddChar (E0 × φ.A) ℂ) :
    H.dir (chr φ ψ) = dirChar (recH H) ψ := by
  refine MulChar.ext fun u => ?_
  rw [H.dir_unit, dirChar_unit]
  rfl

private theorem UpperTheory.Comparison₂.prim_read_surj (φ : Frame) : Function.Surjective (toE φ) := by
  have key : ∀ a : ZMod 2, ∃ s : ℤˣ, Multiplicative.toAdd (LFunctionChainParameters.LHost.sgn2 s) = a := by
    intro a
    fin_cases a
    · exact ⟨1, by simp [LFunctionChainParameters.LHost.sgn2] <;> rfl⟩
    · exact ⟨-1, by simp [LFunctionChainParameters.LHost.sgn2] <;> rfl⟩
  intro x
  obtain ⟨s1, hs1⟩ := key (Multiplicative.toAdd x).1.1
  obtain ⟨s2, hs2⟩ := key (Multiplicative.toAdd x).1.2
  refine ⟨((s2, s1), Multiplicative.ofAdd (Multiplicative.toAdd x).2), ?_⟩
  simp only [toE, MonoidHom.coe_mk, OneHom.coe_mk, hs1, hs2]
  rfl

private theorem UpperTheory.Comparison₂.prim_read_max (y : ℝ) (n : ℕ) (hn : n ∈ Finset.Icc 1 ⌊y⌋₊) :
    max (y / n - 1) 0 = y / n - 1 := by
  obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hn
  have hpos : (0 : ℝ) < n := by exact_mod_cast h1
  have hfl : 0 < ⌊y⌋₊ := by omega
  have hy : 1 ≤ y := Nat.floor_pos.mp hfl
  have hny : (n : ℝ) ≤ y := (Nat.cast_le.mpr h2).trans (Nat.floor_le (by linarith))
  have h1y : 1 ≤ y / n := (one_le_div hpos).mpr hny
  exact max_eq_left (by linarith)

private theorem UpperTheory.Comparison₂.prim_read_Gz (y : ℝ) : Gz y = An.G y := by
  unfold Gz Sz An.G
  rw [Finset.sum_congr rfl fun n hn => congrArg (fun t => An.abelian₂ n * t) (UpperTheory.Comparison₂.prim_read_max y n hn)]
  ring

private theorem UpperTheory.Comparison₂.prim_read_one {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) :
    χ.primitiveCharacter = 1 ↔ χ = 1 := by
  constructor
  · intro h
    rw [← DirichletCharacter.changeLevel_primitiveCharacter χ, h, map_one]
  · rintro rfl
    exact DirichletCharacter.primitiveCharacter_one

theorem UpperTheory.Comparison₂.prim_read :
    ∀ (φ : Frame) (H : HostAx φ) (ell : AddChar (E0 × φ.A) ℂ → ℂ), HostAddCharCompatible H.toHostRaw ell → ∀ ψ : AddChar (E0 × φ.A) ℂ,
      (ψ ≠ 0 → ell ψ = An.logDerivativeAtOne (H.toHostRaw.prim (chr φ ψ)).χ) ∧
        ∀ y, GPsi (arith H.toHostRaw) ell ψ y = An.gChi (H.toHostRaw.prim (chr φ ψ)).χ y := by
  intro φ H ell hell ψ
  unfold HostAddCharCompatible at hell
  set R := H.toHostRaw with hR
  have hdir : R.dir (chr φ ψ) = dirChar (recH R) ψ := prim_read_dir φ R ψ
  have hval : ∀ n : ℕ, n ≠ 0 → (R.prim (chr φ ψ)).χ n = primVal (arith R) ψ n := by
    intro n hn
    show (R.dir (chr φ ψ)).primitiveCharacter n = _
    rw [hdir]
    exact (primitive_value_primitive (H := φ.A) R.condN R.q R.d (recH R) ψ n
      (HostRaw.condN_pos R).ne' hn).symm
  have h1 : ψ ≠ 0 → ell ψ = An.logDerivativeAtOne (R.prim (chr φ ψ)).χ := fun hψ =>
    @hell ψ hψ _ (R.prim (chr φ ψ)).ne _ (R.prim (chr φ ψ)).prim hval
  have hone : (R.prim (chr φ ψ)).χ = 1 ↔ ψ = 0 := by
    show (R.dir (chr φ ψ)).primitiveCharacter = 1 ↔ ψ = 0
    rw [prim_read_one, hdir]
    constructor
    · intro h
      rw [AddChar.eq_zero_iff]
      intro x
      obtain ⟨g, hg⟩ := prim_read_surj φ (Multiplicative.ofAdd x)
      obtain ⟨u, hu⟩ := HostDer.art_surj H.der g
      have hu1 : (dirChar (recH R) ψ) u = 1 := by
        rw [h]
        exact MulChar.one_apply_coe u
      rw [dirChar_unit] at hu1
      have e : recH R u = Multiplicative.ofAdd x := by
        show toE φ (R.art u) = _
        rw [hu, hg]
      rwa [e, toAdd_ofAdd] at hu1
    · rintro rfl
      refine MulChar.ext fun u => ?_
      rw [dirChar_unit, AddChar.zero_apply, MulChar.one_apply_coe]
  refine ⟨h1, fun y => ?_⟩
  by_cases hψ : ψ = 0
  · have hχ : (R.prim (chr φ ψ)).χ = 1 := hone.mpr hψ
    unfold GPsi An.gChi
    rw [if_pos hψ, if_pos hχ, prim_read_Gz]
  · have hχ : (R.prim (chr φ ψ)).χ ≠ 1 := fun h => hψ (hone.mp h)
    unfold GPsi An.gChi
    rw [if_neg hψ, if_neg hχ, ← h1 hψ, An.sumLamChi]
    congr 1
    refine Finset.sum_congr rfl fun n hn => ?_
    have hn0 : n ≠ 0 := by
      have := (Finset.mem_Icc.mp hn).1
      omega
    rw [hval n hn0, prim_read_max y n hn]
end

section

open UpperTheory.Comparison₂ Deduction.CH Formalism Formalism.HC Formalism.D5 Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.ThickSetMeanBounds Formalism.LFunctionChainParameters.LErr
  Formalism.LFunctionChainParameters.LChain Formalism.LFunctionChainParameters.LHost

theorem UpperTheory.Comparison₂.formB :
    ∀ Λ : Level, Λ.FormB := by
  intro Λ la hla θ hθ0 hθ1 hW
  classical
  let weight (ψ : PChar) : ℝ := if ψ = PChar.one then 1 else Λ.wt ψ
  have weight_pos (ψ : PChar) : 0 < weight ψ := by
    unfold weight Level.wt
    split_ifs
    · exact one_pos
    · exact one_pos
    · positivity
  have admissible (ψ : PChar) : ψ.N = 1 ∨ ψ.χ ≠ 1 := by
    by_cases h : ψ.χ = 1
    · left
      have hp := ψ.prim
      rw [DirichletCharacter.IsPrimitive, h, DirichletCharacter.conductor_one] at hp
      exact hp.symm
    · exact Or.inr h
  let F : Deduction.CharFamily :=
    @Deduction.CharFamily.mk Λ.KEPT _ (fun i => i.1.N) (fun i => i.1.ne)
      (fun i => i.1.χ) (fun i => weight i.1) (fun i => weight_pos i.1)
      (fun i => admissible i.1)
  have hG (y : ℝ) : Deduction.Gm F y = Λ.Gm y := by
    change (∑ i : Λ.KEPT, weight i.1 * (Deduction.Gchi i.1.χ y).re) = Λ.Gm y
    rw [Finset.sum_coe_sort Λ.KEPT (fun ψ => weight ψ * (Deduction.Gchi ψ.χ y).re),
      ← Finset.add_sum_erase _ _ Λ.one_mem, Level.Gm, Level.Nt]
    congr 1
    · have hGz : Formalism.Gz y = An.G y := by
        unfold Formalism.Gz Formalism.Sz An.G
        have hsum : (∑ n ∈ Finset.Icc 1 ⌊y⌋₊, ArithmeticFunction.vonMangoldt n * (y / n - 1)) =
            ∑ n ∈ Finset.Icc 1 ⌊y⌋₊, An.abelian₂ n * max (y / n - 1) 0 := by
          apply Finset.sum_congr rfl
          intro n hn
          obtain ⟨hn₁, hn₂⟩ := Finset.mem_Icc.mp hn
          have hn_pos : 0 < n := Nat.zero_lt_of_lt hn₁
          have hny : (n : ℝ) ≤ y := (Nat.le_floor_iff' hn_pos.ne').mp hn₂
          have hnonneg : 0 ≤ y / (n : ℝ) - 1 := by
            rw [sub_nonneg, le_div_iff₀ (Nat.cast_pos.mpr hn_pos), one_mul]
            exact hny
          rw [max_eq_left hnonneg]
        rw [hsum]
        ring
      rw [show weight PChar.one = 1 by simp [weight], one_mul, ← gChi_eq, hGz]
      simp only [An.gChi, PChar.one]
      exact (congrArg Complex.re (ite_eq_left rfl)).trans (Complex.ofReal_re _)
    · refine Finset.sum_congr rfl fun ψ hψ => ?_
      have hne : ψ ≠ PChar.one := Finset.ne_of_mem_erase hψ
      simp only [weight, ite_eq_right hne, gChi_eq]
  have hZ (h : Deduction.ZeroFree F θ) : Λ.ZeroFreeAbove θ := by
    intro ψ hψ s hs
    exact h ⟨ψ, hψ⟩ s hs
  apply hZ
  refine Deduction.zeroFree_of_rpow_window F (δ := la - 1) (C := 1) hθ0 hθ1 (by linarith) fun Y₀ => ?_
  obtain ⟨Y, hY, hx⟩ := hW Y₀
  refine ⟨Y, hY, fun y hy => ?_⟩
  have h1 : (1 : ℝ) + (la - 1) = la := by ring
  rw [h1] at hy
  rw [hG, one_mul]
  exact hx y hy.1 hy.2
end
