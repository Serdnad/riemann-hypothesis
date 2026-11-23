module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RedIdeal
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RamifiedLineCharacters.MemRamLine
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RamifiedLineCharacters.CocConj
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
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

theorem UpperTheory.V.Ws.Gys.cupSwap :
    ∀ {O Γ R : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] [CommRing R] (Φ : Fr O Γ) (a : O →+* R) (w w' : ℤ × ℤ) (x y z : Γ → R) (m n : Φ.ι → R), Φ.Coc a w x → Φ.LocTriv a w x m → Φ.Coc a w' y → Φ.LocTriv a w' y n →
      Φ.Cup a w w' x y z m → Φ.Cup a w' w y x (x * y - z) n := by
  intro O Γ R _ _ _ _ Φ a w w' x y z m n hx hm hy hn hz
  have e : ∀ g, a (Φ.rt (w + w') g) = a (Φ.rt w g) * a (Φ.rt w' g) := fun g => by
    rw [Fr.rt_add, Units.val_mul, map_mul]
  refine ⟨?_, fun g h => ?_, fun g hg => ?_, fun v => ?_⟩
  · exact (hx.lc.comp₂ hy.lc (· * ·)).comp₂ hz.lc (· - ·)
  · simp only [Pi.sub_apply, Pi.mul_apply]
    rw [add_comm w' w, hx.coc, hy.coc, hz.coc, e]
    ring
  · simp only [Pi.sub_apply, Pi.mul_apply]
    rw [hx.kill g hg, hz.kill g hg, zero_mul, sub_zero]
  · obtain ⟨o, ho⟩ := hz.loc v
    refine ⟨m v * n v - o, fun s hs => ?_⟩
    simp only [Pi.sub_apply, Pi.mul_apply]
    rw [add_comm w' w, ho s hs, e, hm v s hs, hn v s hs]
    ring
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

theorem UpperTheory.V.Ws.Gys.descend :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (R M : Type) [CommRing R] [AddCommGroup M] [Module R M] [Finite M] [TopologicalSpace M] [DiscreteTopology M] (ρ : Representation R (G F Ω) M) (S : Finset (HeightOneSpectrum (𝓞 F))), ContAction ρ → UnrOut ρ S →
      ∃ ρS : Representation R (GS Ω (S : Set (HeightOneSpectrum (𝓞 F)))) M, ρS.comp (toGS Ω _) = ρ ∧ ContAction ρS := by
  intro F Ω _ _ _ _ _ R M _ _ _ _ _ _ ρ S hρ hU
  have hclosed : IsClosed (ρ.ker : Set (G F Ω)) := by
    have hset : (ρ.ker : Set (G F Ω)) = ⋂ m : M, {g | ρ g m = m} := by
      ext g
      simp only [SetLike.mem_coe, MonoidHom.mem_ker, Set.mem_iInter, Set.mem_setOf_eq]
      constructor
      · intro h m
        rw [h]
        rfl
      · intro h
        exact LinearMap.ext h
    rw [hset]
    refine isClosed_iInter fun m => ?_
    have hc : Continuous fun g : G F Ω => ρ g m :=
      hρ.comp (continuous_id.prodMk continuous_const)
    exact isClosed_eq hc continuous_const
  have hle : NS Ω (S : Set (HeightOneSpectrum (𝓞 F))) ≤ ρ.ker := by
    unfold NS
    refine Subgroup.topologicalClosure_minimal _ ?_ hclosed
    refine Subgroup.normalClosure_le_normal ?_
    intro g hg
    simp only [Set.mem_iUnion, Set.mem_setOf_eq] at hg
    obtain ⟨v, hv, A, hA, hgA⟩ := hg
    exact hU v hv A hA g (mem_Ine.mpr hgA)
  refine ⟨QuotientGroup.lift _ ρ hle, ?_, ?_⟩
  · exact MonoidHom.ext fun g => rfl
  · have h2 := (QuotientGroup.isOpenQuotientMap_mk (N := NS Ω (S : Set (HeightOneSpectrum (𝓞 F)))).prodMap
      (IsOpenQuotientMap.id (X := M))).continuous_comp_iff
      (g := fun p : GS Ω (S : Set (HeightOneSpectrum (𝓞 F))) × M => (QuotientGroup.lift _ ρ hle) p.1 p.2)
    exact h2.mp hρ
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

theorem UpperTheory.V.Ws.Gys.selMem :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (R M : Type) [CommRing R] [AddCommGroup M] [Module R M] [Finite M] [TopologicalSpace M] [DiscreteTopology M] (S₀ S : Finset (HeightOneSpectrum (𝓞 F))) (ρ : Representation R (GS Ω (S : Set (HeightOneSpectrum (𝓞 F)))) M), S₀ ⊆ S →
      (∀ v ∈ S, v ∉ S₀ → TrivAt l (ρ.comp (toGS Ω _)) v) → ∀ Av : S → ValuationSubring Ω, (∀ v, IsPlaceOver (Av v) v.1) → ∀ (m0 : M) (f : Z1 ρ),
        Submodule.Quotient.mk f ∈ gysSel S₀ S ρ Av m0 →
        (fun g => f.1 (toGS Ω _ g)) ∈ Zunr (ρ.comp (toGS Ω _)) S ∧
        (∀ v ∈ S₀, ∀ A, IsPlaceOver A v → ∃ m, ∀ g ∈ Dec (F := F) A, f.1 (toGS Ω _ g) = ρ (toGS Ω _ g) m - m) ∧
        ∀ v : S, v.1 ∉ S₀ → ∀ g ∈ Ine (F := F) (Av v), f.1 (toGS Ω _ g) ∈ Submodule.span R {m0} := by
  intro F Ω _ _ _ _ _ l _ R M _ _ _ _ _ _ S₀ S ρ hS htriv Av hA m0 f hf
  have hZ : (fun g => f.1 (toGS Ω _ g)) ∈ Z1 (ρ.comp (toGS Ω _) : Representation R (G F Ω) M) :=
    ⟨f.2.1.comp QuotientGroup.continuous_mk, fun a b => by
      have := f.2.2 (toGS Ω _ a) (toGS Ω _ b)
      rw [← map_mul] at this
      exact this⟩
  have hloc := (mem_Sel _ _ _ _ _).1 hf
  refine ⟨⟨hZ, fun v hv A hAv g hg => ?_⟩, fun v hv A hAv => ?_, fun v hv g hg => ?_⟩
  · have h1 : f.1 1 = 0 := by
      have := f.2.2 1 1
      rw [one_mul, map_one] at this
      exact left_eq_add.1 this
    have h2 : toGS Ω (S : Set (HeightOneSpectrum (𝓞 F))) g = 1 := by
      refine (QuotientGroup.eq_one_iff g).2 ?_
      apply Subgroup.le_topologicalClosure
      apply Subgroup.subset_normalClosure
      simp only [Set.mem_iUnion]
      exact ⟨v, hv, A, hAv, hg⟩
    show f.1 (toGS Ω _ g) = 0
    rw [h2, h1]
  · have h := hloc ⟨v, hS hv⟩
    rw [show gysL S₀ S ρ Av m0 ⟨v, hS hv⟩ = ⊥ from if_pos hv, Submodule.mem_bot] at h
    obtain ⟨m, hm⟩ := (mem_coboundaries1 _ _).1 ((Submodule.Quotient.mk_eq_zero _).1 h)
    exact (UpperTheory.V.Ws.Gys.cocConj F Ω R M (ρ.comp (toGS Ω _)) _ hZ v (Av ⟨v, hS hv⟩) A (hA ⟨v, hS hv⟩) hAv).1
      ⟨m, fun g hg => hm ⟨g, hg⟩⟩
  · have h := hloc v
    rw [show gysL S₀ S ρ Av m0 v = ramLine (ρ.comp (locFam S Av v)) ((Ine (F := F) (Av v)).subgroupOf (Dec (F := F) (Av v))) m0
      from if_neg hv, mem_ramLine] at h
    obtain ⟨f', h1, h2⟩ := h
    obtain ⟨m, hm⟩ := (mem_coboundaries1 _ _).1 ((Submodule.Quotient.eq _).1 h2)
    have hd : g ∈ Dec (F := F) (Av v) := Ine_le_Dec _ hg
    have h3 := hm ⟨g, hd⟩
    have h4 : ρ (toGS Ω _ g) = 1 := (htriv v.1 v.2 hv (Av v) (hA v) g hd).1
    have h5 : f'.1 ⟨g, hd⟩ - f.1 (toGS Ω _ g) = ρ (toGS Ω _ g) m - m := h3
    rw [h4, Module.End.one_apply, sub_self, sub_eq_zero] at h5
    rw [← h5]
    exact h1 ⟨g, hd⟩ hg
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem map_mul_inv_ne_one_of_isUnit_map_sub {O k : Type} [CommRing O] [Field k] (a : O →+* k) (u v : Oˣ)
    (h : IsUnit (a ↑u - a ↑v)) : a ↑(u * v⁻¹) ≠ 1 := by
  intro h1
  have h2 : a ↑(u * v⁻¹) * a ↑v = 1 * a ↑v := by rw [h1]
  rw [Units.val_mul, ← map_mul, mul_assoc, Units.inv_mul, mul_one, one_mul] at h2
  exact h.ne_zero (sub_eq_zero.2 h2)

theorem UpperTheory.V.Ws.Gys.rootCharacters_ne_one_at_basepoint :
    ∀ {O Γ k : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] [Field k] (Φ : Fr O Γ) (a : O →+* k), Φ.Ok a → a (Φ.rt (-wAl) Φ.g0) ≠ 1 ∧ a (Φ.rt (-wPs) Φ.g0) ≠ 1 ∧ a (Φ.rt (-wAl + -wPs) Φ.g0) ≠ 1 := by
  intro O Γ k _ _ _ _ Φ a hΦ
  have e1 : Φ.rt (-wAl) Φ.g0 = Φ.χ 1 Φ.g0 * (Φ.χ 0 Φ.g0)⁻¹ := by
    simp [Fr.rt, wAl]
  have e2 : Φ.rt (-wPs) Φ.g0 = Φ.χ 2 Φ.g0 * (Φ.χ 0 Φ.g0)⁻¹ := by
    simp [Fr.rt, wPs]
  have hm : Φ.χ 1 Φ.g0 * Φ.χ 2 Φ.g0 = Φ.χ 0 Φ.g0 * Φ.χ 3 Φ.g0 := by
    have h1 := hΦ.mul 1 Φ.g0
    have h0 := hΦ.mul 0 Φ.g0
    have r1 : Fin.rev (1 : Fin 4) = 2 := by decide
    have r0 : Fin.rev (0 : Fin 4) = 3 := by decide
    rw [r1] at h1
    rw [r0] at h0
    rw [h1, h0]
  have e3 : Φ.rt (-wAl + -wPs) Φ.g0 = Φ.χ 3 Φ.g0 * (Φ.χ 0 Φ.g0)⁻¹ := by
    rw [Fr.rt_add, e1, e2, mul_mul_mul_comm, hm, mul_comm (Φ.χ 0 Φ.g0), mul_assoc, mul_inv_cancel_left]
  refine ⟨?_, ?_, ?_⟩
  · rw [e1]
    exact map_mul_inv_ne_one_of_isUnit_map_sub a _ _ (hΦ.dist 1 0 (by decide))
  · rw [e2]
    exact map_mul_inv_ne_one_of_isUnit_map_sub a _ _ (hΦ.dist 2 0 (by decide))
  · rw [e3]
    exact map_mul_inv_ne_one_of_isUnit_map_sub a _ _ (hΦ.dist 3 0 (by decide))
end
