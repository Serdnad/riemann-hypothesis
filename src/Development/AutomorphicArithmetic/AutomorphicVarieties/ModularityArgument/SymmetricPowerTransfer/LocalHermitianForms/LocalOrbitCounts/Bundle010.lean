module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.Bundle001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.BilinearSmul.BSmulRight
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.Bundle001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.SplitUnitElements.Bundle002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.Bundle002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.ExistsUnitOneAddGenerator
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.Bundle007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.Bundle009
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.Bundle003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.OrbitImp
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.NormOneIsCoboundaryUnramifiedQuadratic
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.Bundle002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.Bundle006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.Bundle008
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.Bundle004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.SumShift
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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

@[expose] public section

section

open QuadraticAlgebra UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc

open Matrix in
theorem UpperTheory.V.Z.Sym.Loc.orbEq : UpperTheory.V.Z.Sym.Loc.OrbEq := by
  set_option synthInstance.maxHeartbeats 200000 in
    intro O K _ _ _ _ _ Δ τ hLoc c d m _ δ ι P hM
    have hmv : ∀ (a b : U3 Δ) (v : Fin 3 → Lsq K Δ),
        ((a * b : U3 Δ) : Matrix (Fin 3) (Fin 3) (Lsq K Δ)).mulVec v
          = (a : Matrix (Fin 3) (Fin 3) (Lsq K Δ)).mulVec ((b : Matrix (Fin 3) (Fin 3) (Lsq K Δ)).mulVec v) := by
      intro a b v
      rw [Submonoid.coe_mul, Matrix.mulVec_mulVec]
    have hmv1 : ∀ v : Fin 3 → Lsq K Δ, ((1 : U3 Δ) : Matrix (Fin 3) (Fin 3) (Lsq K Δ)).mulVec v = v := by
      intro v
      simp
    have hinv : ∀ (a : U3 Δ) (v : Fin 3 → Lsq K Δ),
        ((a⁻¹ : U3 Δ) : Matrix (Fin 3) (Fin 3) (Lsq K Δ)).mulVec ((a : Matrix (Fin 3) (Fin 3) (Lsq K Δ)).mulVec v) = v := by
      intro a v
      rw [← hmv, inv_mul_cancel, hmv1]
    have hinv' : ∀ (a : U3 Δ) (v : Fin 3 → Lsq K Δ),
        (a : Matrix (Fin 3) (Fin 3) (Lsq K Δ)).mulVec (((a⁻¹ : U3 Δ) : Matrix (Fin 3) (Fin 3) (Lsq K Δ)).mulVec v) = v := by
      intro a v
      rw [← hmv, mul_inv_cancel, hmv1]
    have hA : ∀ (A : Matrix (Fin 3) (Fin 3) (Lsq K Δ)) (v : Fin 3 → Lsq K Δ),
        (∀ i j, IsInt O (A i j)) → (∀ i, IsInt O (v i)) → ∀ i, IsInt O (A.mulVec v i) := by
      intro A v hA hv i
      simp only [Matrix.mulVec, dotProduct]
      exact IsIntegral.sum _ (fun j _ => (hA i j).mul (hv j))
    have hKUint : ∀ k ∈ KU O Δ, ∀ v : Fin 3 → Lsq K Δ, (∀ i, IsInt O (v i)) →
        ∀ i, IsInt O ((k : Matrix (Fin 3) (Fin 3) (Lsq K Δ)).mulVec v i) := by
      intro k hk v hv
      have hk' : ∀ i j, IsInt O ((k : Matrix (Fin 3) (Fin 3) (Lsq K Δ)) i j)
          ∧ IsInt O (star ((k : Matrix (Fin 3) (Fin 3) (Lsq K Δ)) i j)) := hk
      exact hA _ v (fun i j => (hk' i j).1) hv
    have hKUof : ∀ h : U3 Δ, (∀ v : Fin 3 → Lsq K Δ, (∀ i, IsInt O (v i)) →
        ∀ i, IsInt O ((h : Matrix (Fin 3) (Fin 3) (Lsq K Δ)).mulVec v i)) → h ∈ KU O Δ := by
      intro h H
      have he : ∀ i j, IsInt O ((h : Matrix (Fin 3) (Fin 3) (Lsq K Δ)) i j) := by
        intro i j
        have hs : ∀ k, IsInt O ((Pi.single j (1 : Lsq K Δ) : Fin 3 → Lsq K Δ) k) := by
          intro k
          rcases eq_or_ne k j with rfl | hkj
          · simpa using (isIntegral_one : IsIntegral O (1 : Lsq K Δ))
          · simpa [Pi.single_apply, hkj] using (isIntegral_zero : IsIntegral O (0 : Lsq K Δ))
        have := H _ hs i
        simpa [Matrix.mulVec_single_one] using this
      exact fun i j => ⟨he i j, OE.int_star hLoc (he i j)⟩
    obtain ⟨L, hLm⟩ : ∃ L : U3 Δ → Set (Sp Δ τ), ∀ g x, x ∈ L g ↔
        ∀ i, IsInt O (((g⁻¹ : U3 Δ) : Matrix (Fin 3) (Fin 3) (Lsq K Δ)).mulVec (P x) i) :=
      ⟨fun g => {x | ∀ i, IsInt O (((g⁻¹ : U3 Δ) : Matrix (Fin 3) (Fin 3) (Lsq K Δ)).mulVec (P x) i)}, fun _ _ => Iff.rfl⟩
    have LD : ∀ a b : U3 Δ, a⁻¹ * b ∈ KU O Δ → L b = L a := by
      intro a b hk
      ext x
      rw [hLm, hLm]
      have hb : b = a * (a⁻¹ * b) := (mul_inv_cancel_left a b).symm
      set k := a⁻¹ * b
      rw [hb, _root_.mul_inv_rev, hmv]
      constructor
      · intro h
        have := hKUint k hk _ h
        rwa [hinv'] at this
      · intro h
        exact hKUint _ (inv_mem hk) _ h
    have Lsame : ∀ a b : U3 Δ, L a = L b → a⁻¹ * b ∈ KU O Δ := by
      intro a b h
      apply hKUof
      intro v hv
      have hx : P.symm ((b : Matrix (Fin 3) (Fin 3) (Lsq K Δ)).mulVec v) ∈ L b := by
        rw [hLm, LinearEquiv.apply_symm_apply, hinv]
        exact hv
      rw [← h, hLm, LinearEquiv.apply_symm_apply] at hx
      rwa [hmv]
    have hstar : ∀ (g : U3 Δ) (v : Fin 3 → Lsq K Δ),
        ((theta Δ g : U3 Δ) : Matrix (Fin 3) (Fin 3) (Lsq K Δ)).mulVec v
          = star ((g : Matrix (Fin 3) (Fin 3) (Lsq K Δ)).mulVec (star v)) := by
      intro g v
      show ((g : Matrix (Fin 3) (Fin 3) (Lsq K Δ)).map star).mulVec v = _
      funext i
      simp [Matrix.mulVec, dotProduct, Matrix.map_apply, star_sum, star_mul']
    have Gconv : ∀ g : U3 Δ, IsFix O c d m (L g) → g⁻¹ * δ * theta Δ g ∈ KU O Δ := by
      intro g hF
      apply hKUof
      intro v hv
      have hx : P.symm ((g : Matrix (Fin 3) (Fin 3) (Lsq K Δ)).mulVec (star v)) ∈ L g := by
        rw [hLm, LinearEquiv.apply_symm_apply, hinv]
        intro i
        exact OE.int_star hLoc (hv i)
      have hsx : semi d (P.symm ((g : Matrix (Fin 3) (Fin 3) (Lsq K Δ)).mulVec (star v))) ∈ L g := by
        rw [← hF.stab]
        exact ⟨_, hx, rfl⟩
      rw [hLm, hM.semi, LinearEquiv.apply_symm_apply, ← hstar] at hsx
      rwa [hmv, hmv]
    have hkrel : ∀ g : U3 Δ, g⁻¹ * δ * theta Δ g ∈ KU O Δ ↔ IsFix O c d m (L g) := by
      intro g
      refine ⟨fun h => ?_, Gconv g⟩
      have := One.fixg O K Δ τ hLoc c d m δ ι P hM g h
      convert this using 1
      ext x
      exact hLm g x
    have torinv : ∀ (t : (Etau K τ)ˣ) (x : Sp Δ τ), tor Δ t (tor Δ t⁻¹ x) = x := by
      intro t x
      apply P.injective
      rw [hM.tor, hM.tor, map_inv, hinv']
    have Ltor : ∀ (t : (Etau K τ)ˣ) (g : U3 Δ), L (ι t * g) = tor Δ t '' L g := by
      intro t g
      ext x
      rw [hLm]
      constructor
      · intro hx
        refine ⟨tor Δ t⁻¹ x, ?_, torinv t x⟩
        rw [hLm, hM.tor, map_inv]
        rwa [_root_.mul_inv_rev, hmv] at hx
      · rintro ⟨y, hy, rfl⟩
        rw [hLm] at hy
        rw [_root_.mul_inv_rev, hmv, hM.tor, hinv]
        exact hy
    have heq : ∀ (t : (Etau K τ)ˣ) (y : U3 Δ ⧸ KU O Δ),
        L (Quotient.out ((ι t) • y)) = tor Δ t '' L (Quotient.out y) := by
      intro t y
      have hq : (QuotientGroup.mk (ι t * Quotient.out y) : U3 Δ ⧸ KU O Δ) = (ι t) • y := by
        conv_rhs => rw [← QuotientGroup.out_eq' y]
        rfl
      have hq2 : (QuotientGroup.mk (ι t * Quotient.out y) : U3 Δ ⧸ KU O Δ)
          = QuotientGroup.mk (Quotient.out ((ι t) • y)) := by
        rw [QuotientGroup.out_eq', hq]
      rw [LD _ _ (QuotientGroup.eq.mp hq2)]
      exact Ltor t (Quotient.out y)
    unfold uOrb lcount orb
    refine @wTrans _ _ _ inferInstance (MulAction.compHom (U3 Δ ⧸ KU O Δ) ι) (torAct Δ τ) (Cint O τ) _ _ (fun y S => S = L (Quotient.out y)) ?_ ?_ ?_ ?_ ?_ ?_
    · intro t y
      beta_reduce
      split_ifs with h1 h2 h3
      · rfl
      · exact absurd ((hkrel _).mpr ((isFix_tor c d m t _).mp
          ((congrArg (IsFix O c d m) (heq t y)).to_iff.mp ((hkrel _).mp h1)))) h2
      · exact absurd ((hkrel _).mpr ((congrArg (IsFix O c d m) (heq t y)).to_iff.mpr
          ((isFix_tor c d m t _).mpr ((hkrel _).mp h3)))) h1
      · rfl
    · intro t S
      split_ifs with h1 h2 h3
      · rfl
      · exact absurd ((isFix_tor c d m t S).mp h1) h2
      · exact absurd ((isFix_tor c d m t S).mpr h3) h1
      · rfl
    · intro t y S hR
      subst hR
      exact (heq t y).symm
    · intro y S hR
      subst hR
      beta_reduce
      split_ifs with h1 h2 h3
      · rfl
      · exact absurd ((hkrel _).mp h1) h2
      · exact absurd ((hkrel _).mpr h3) h1
      · rfl
    · intro y _
      exact ⟨_, rfl, fun S h => h⟩
    · intro S hS
      have hF : IsFix O c d m S := by
        by_contra h
        simp [h] at hS
      obtain ⟨s, hs⟩ := hF.fg
      set M : Submodule O (Fin 3 → Lsq K Δ) :=
        Submodule.map ((P : Sp Δ τ →ₗ[Lsq K Δ] (Fin 3 → Lsq K Δ)).restrictScalars O)
          (Submodule.span O (s : Set (Sp Δ τ))) with hMdef
      have hmem : ∀ v, v ∈ M ↔ P.symm v ∈ S := by
        intro v
        rw [hs, hMdef, Submodule.mem_map, SetLike.mem_coe]
        constructor
        · rintro ⟨x, hx, rfl⟩
          simpa using hx
        · intro h
          exact ⟨_, h, by simp⟩
      have hFG : M.FG := Submodule.FG.map _ (Submodule.fg_span (Finset.finite_toSet s))
      obtain ⟨g, hg⟩ := OE.ortho hLoc M hFG (by
        intro w
        rw [hmem, hF.dual]
        constructor
        · intro h u hu
          have := h _ ((hmem u).mp hu)
          rw [hM.form, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply] at this
          exact this
        · intro h x hx
          rw [hM.form, LinearEquiv.apply_symm_apply]
          exact h (P x) ((hmem _).mpr (by simpa using hx)))
      have hSL : S = L g := by
        ext x
        rw [hLm, ← hg, hmem, LinearEquiv.symm_apply_apply]
      refine ⟨QuotientGroup.mk g, ?_, ?_⟩
      · show S = L (Quotient.out (QuotientGroup.mk g : U3 Δ ⧸ KU O Δ))
        rw [hSL]
        exact (LD _ _ (QuotientGroup.eq.mp (QuotientGroup.out_eq' (QuotientGroup.mk g : U3 Δ ⧸ KU O Δ)).symm)).symm
      · intro y hy
        rw [← QuotientGroup.out_eq' y]
        apply QuotientGroup.eq.mpr
        apply Lsame
        rw [← hSL]
        exact hy.symm
end

section

open QuadraticAlgebra UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob

theorem UpperTheory.V.Z.Sym.Loc.finD : UpperTheory.V.Z.Sym.Loc.FinD := by
  classical
  intro O K _ _ _ _ _ Δ τ L hτ γ j hγ hj
  obtain ⟨φ, h1, h2, -, h4⟩ := dIso O K Δ L
  obtain ⟨j', hj'γ, hj'tr, hj'⟩ := h4 τ γ j hγ hj
  have hZD : ∀ g : DX Δ, g ∈ ZD Δ ↔ ∃ z, IsScal z g := by
    intro g
    simp only [ZD, Subgroup.mem_subgroupOf, MonoidHom.mem_range, MonoidHom.comp_apply, IsScal]
    constructor
    · rintro ⟨z, hz⟩
      refine ⟨z, ?_⟩
      show ((g : GL (Fin 2) (Lsq K Δ)) : Matrix (Fin 2) (Fin 2) (Lsq K Δ)) = _
      rw [← hz]
      first | rfl | simp [Matrix.GeneralLinearGroup.scalar]
    · rintro ⟨z, hz⟩
      refine ⟨z, ?_⟩
      apply Units.ext
      rw [show ((g : GL (Fin 2) (Lsq K Δ)) : Matrix (Fin 2) (Fin 2) (Lsq K Δ)) = Glob.mt g from rfl, hz]
      first | rfl | simp [Matrix.GeneralLinearGroup.scalar]
  have hmap : (ZD Δ ⊔ KD Δ O).map φ.toMonoidHom = ZK O K := by
    rw [Subgroup.map_sup]
    unfold ZK
    congr 1
    · ext x
      rw [Subgroup.mem_map_equiv, hZD, MonoidHom.mem_range]
      constructor
      · rintro ⟨z, hz⟩
        exact ⟨z, by rw [← (h2 z _).1 hz]; simp⟩
      · rintro ⟨z, rfl⟩
        exact ⟨z, (h2 z _).2 (by simp)⟩
    · ext x
      rw [Subgroup.mem_map_equiv, ← h1]
      simp
  have hmem : ∀ g, g ∈ ZD Δ ⊔ KD Δ O ↔ φ g ∈ ZK O K := by
    intro g
    rw [← hmap, Subgroup.mem_map_equiv]
    simp
  have hgen : ∀ z : (Etau K τ)ˣ, (z : Etau K τ).im ≠ 0 → ∃ S : Finset (DX Δ), ∀ y : DX Δ,
      y⁻¹ * j z * y ∈ ZD Δ ⊔ KD Δ O → ∃ t, ∃ s ∈ S, ∃ u ∈ ZD Δ ⊔ KD Δ O, y = j t * s * u := by
    intro z hz
    obtain ⟨s, hs⟩ := finG O K Δ τ L hτ j' hj'tr z hz
    refine ⟨s.image φ.symm, ?_⟩
    intro y hy
    rw [hmem] at hy
    simp only [map_mul, map_inv, hj'] at hy
    obtain ⟨t, x, hx, k, hk, hyk⟩ := hs (φ y) hy
    refine ⟨t, φ.symm x, Finset.mem_image_of_mem _ hx, φ.symm k, by rw [hmem]; simp [hk], ?_⟩
    apply φ.injective
    simp [map_mul, hj', hyk]
  obtain ⟨a, ha⟩ := exists_a (K := K) (τ := τ)
  have hγa : γ = j a := by
    apply φ.injective
    rw [hj']
    apply Units.ext
    rw [← hj'γ]
    simp [ha]
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨S, hS⟩ := hgen a (by rw [ha]; simp)
    refine ⟨S, ?_⟩
    intro y hy
    apply hS y
    have hK : y⁻¹ * γ * y ∈ KD Δ O := by
      by_contra hn
      apply hy
      simp [one, hn]
    rw [← hγa]
    exact Subgroup.mem_sup_right hK
  · intro z hz χ
    obtain ⟨S, hS⟩ := hgen z (by rw [hz]; simp)
    refine ⟨S, ?_⟩
    intro y hy
    apply hS y
    unfold fZD at hy
    split_ifs at hy with hh
    · obtain ⟨z0, s0, hsc, hk⟩ := hh
      have hs0 : s0 ∈ ZD Δ := (hZD s0).2 ⟨z0, hsc⟩
      have := (ZD Δ ⊔ KD Δ O).mul_mem (Subgroup.mem_sup_left hs0) (Subgroup.mem_sup_right hk)
      simpa using this
    · exact absurd rfl hy
  · intro y
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective y
    have hst : Subgroup.comap j (MulAction.stabilizer (DX Δ) (g : DX Δ ⧸ ZD Δ ⊔ KD Δ O)) =
        Subgroup.comap (jU j') (Subgroup.comap (MulAut.conj (φ g)⁻¹).toMonoidHom (ZK O K)) := by
      ext t
      simp only [Subgroup.mem_comap, MulAction.mem_stabilizer_iff, MulAction.Quotient.smul_mk,
        smul_eq_mul, QuotientGroup.eq, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
      rw [← Subgroup.inv_mem_iff, show ((j t * g)⁻¹ * g)⁻¹ = g⁻¹ * j t * g by group, hmem]
      simp [hj']
    rw [hst]
    exact stabG O K Δ τ L hτ j' hj'tr (φ g)
end

section

open QuadraticAlgebra UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob

theorem UpperTheory.V.Z.Sym.Loc.oneD : UpperTheory.V.Z.Sym.Loc.OneD := by
  intro O K _ _ _ _ _ Δ τ L hτ γ j h1 h2 hγ hD
  obtain ⟨φ, p1, p2, p3, p4⟩ := dIso O K Δ L
  obtain ⟨j', q1, q2, q3⟩ := p4 τ γ j h1 h2
  have sc : ∀ z : Kˣ, IsScal z (φ.symm (Matrix.GeneralLinearGroup.scalar (Fin 2) z)) := fun z => (p2 _ _).2 (by simp)
  have hZ : ∀ g, g ∈ ZD Δ ⊔ KD Δ O ↔ φ g ∈ ZK O K := fun g => by
    constructor
    · intro h
      refine (sup_le ?_ ?_ : ZD Δ ⊔ KD Δ O ≤ (ZK O K).comap φ.toMonoidHom) h
      · rintro s ⟨z, hz⟩
        exact Subgroup.mem_sup_left ⟨z, ((p2 z s).1 (congrArg Units.val hz).symm).symm⟩
      · exact fun k hk => Subgroup.mem_sup_right ((p1 k).2 hk)
    · intro h
      obtain ⟨z, k, e⟩ := mem_ZK.1 h
      rw [← φ.symm_apply_apply g, e, map_mul]
      exact mul_mem (Subgroup.mem_sup_left ⟨z, Units.ext (sc z).symm⟩) (Subgroup.mem_sup_right ((p1 _).1 (by rw [φ.apply_symm_apply]; exact ⟨k, rfl⟩)))
  obtain ⟨a, ha⟩ := exists_a (K := K) (τ := τ)
  have ea : j a = γ := φ.injective (by rw [q3]; exact Units.ext (by rw [← q1, ← ha]; rfl))
  have back : ∀ y t x k, k ∈ ZK O K → φ y = jU j' t * x * k → ∃ u ∈ ZD Δ ⊔ KD Δ O, y = j t * φ.symm x * u := fun y t x k hk e =>
    ⟨φ.symm k, (hZ _).2 (by simpa using hk), φ.injective (by simp [e, q3])⟩
  obtain ⟨k₀, hk₀⟩ := (p1 γ).2 hγ
  obtain ⟨G1, G2⟩ := oneG O K Δ τ L j' q2 (fun s t => ⟨k₀ s t, by rw [q1, ← hk₀]; rfl⟩) hD
  have main : ∀ z : (Etau K τ)ˣ, ((z : Etau K τ) = ω ∨ (z : Etau K τ) = 1 + ω) → ∀ y, y⁻¹ * j z * y ∈ ZD Δ ⊔ KD Δ O →
      ∃ t, ∃ u ∈ ZD Δ ⊔ KD Δ O, y = j t * u := fun z hz y hy => by
    obtain ⟨t, k, hk, e⟩ := ((G2 z hz).2 (φ y)).1 (by simpa [q3] using (hZ _).1 hy)
    obtain ⟨u, hu, e'⟩ := back y t 1 k hk (by simpa using e)
    exact ⟨t, u, hu, by simpa using e'⟩
  refine ⟨?_, ea ▸ main a (.inl ha), fun z hz => ⟨(p1 _).1 (q3 z ▸ (G2 z (.inr hz)).1), main z (.inr hz)⟩⟩
  rw [← G1]
  ext t
  rw [Subgroup.mem_comap, Subgroup.mem_comap, hZ, q3]
end

section

open QuadraticAlgebra UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc

private theorem inv_norm {O K : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] {Δ τ : K} (L : IsLoc O Δ)
    {c : K} {d m : EL Δ τ} (h : IsDat c d m) : ∀ t ∈ NE τ, ∀ x : Kˣ,
    lcount O c d (((t * x : Kˣ) : K) • m) = lcount O c d ((x : K) • m) := fun t ht x => by
  rw [Units.val_mul, mul_smul]
  exact lcountNorm O K Δ τ L c d _ (datSmul K Δ τ c d m h x) t ht

theorem UpperTheory.V.Z.Sym.Loc.kapRam : UpperTheory.V.Z.Sym.Loc.KapRam := by
  intro O K _ _ _ _ _ Δ τ L c d m h hτ hodd
  obtain ⟨a, rfl⟩ := hτ
  have h2 := L.two
  have hu : IsUnit (2 - a) := by
    by_contra hn
    apply hodd
    have hp : IsUnit (2 + a) := by
      by_contra hp
      have hsum := IsLocalRing.nonunits_add hn hp
      apply hsum
      have e : (2 - a) + (2 + a) = 2 * 2 := by ring
      rw [e]
      exact h2.mul h2
    refine ⟨hp.unit, 1, one_ne_zero, ?_⟩
    simp [map_add (f := _), map_ofNat]
  obtain ⟨v, hv⟩ := hu
  have hv' : algebraMap O K (v : O) = 2 - algebraMap O K a := by
    rw [hv, map_sub, map_ofNat]
  have hex : ∃ u : Oˣ, algebraMap O K ↑u = 2 - algebraMap O K a := ⟨v, hv'⟩
  refine ⟨hex, ?_⟩
  have hD : ¬ EvenVal O (algebraMap O K a ^ 2 - 4) := by
    rintro ⟨u, s, hs0, hus⟩
    apply hodd
    refine ⟨-(u * v⁻¹), s, hs0, ?_⟩
    have hw : algebraMap O K (v : O) * algebraMap O K ((v⁻¹ : Oˣ) : O) = 1 := by
      rw [← map_mul, Units.mul_inv, map_one]
    rw [hv'] at hw
    simp only [Units.val_neg, Units.val_mul, map_neg, map_mul]
    linear_combination (-(algebraMap O K ((v⁻¹ : Oˣ) : O))) * hus + (-(2 + algebraMap O K a)) * hw
  have hreg := h.reg
  obtain ⟨ε, hε⟩ := ramUnit O K Δ L _ hreg hD
  have hinv : ∀ t ∈ NE (algebraMap O K a), ∀ x : Kˣ,
      lcount O c d (((t * x : Kˣ) : K) • m) = lcount O c d ((x : K) • m) :=
    fun t ht x => inv_norm L h t ht x
  have hg : ((Units.map (algebraMap O K : O →* K) ε : Kˣ) : K) = algebraMap O K ε := rfl
  obtain ⟨_, h2', _⟩ := sumShift O K Δ _ L hreg (fun y : Kˣ => lcount O c d ((y : K) • m)) hinv
    (Units.map (algebraMap O K : O →* K) ε)
  have hshift : ∀ x : Kˣ, lcount O c d (((x * Units.map (algebraMap O K : O →* K) ε : Kˣ) : K) • m)
      = lcount O c d ((x : K) • m) := by
    intro x
    rw [Units.val_mul, hg, mul_comm, mul_smul]
    exact splitM O K Δ _ L c d _ (datSmul K Δ _ c d m h x) ⟨a, rfl⟩ hex ε
  simp only [hshift, hg, hε] at h2'
  have h3 : kapSum O c d m = -1 * kapSum O c d m := by
    unfold kapSum
    exact h2'
  linear_combination h3 / 2
end
