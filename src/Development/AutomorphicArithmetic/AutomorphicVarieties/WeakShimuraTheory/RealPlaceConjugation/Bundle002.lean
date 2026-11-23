module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RbUVal
public import Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.ModulusAdjoinISqrtNegPrimes
import Mathlib.Algebra.Module.StablyFree.Basic
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RealPlaceConjugation.Bundle001
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.GroupTheory.Nilpotent
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
import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Two
open scoped Classical

private theorem exists_natCard_eq_pow_and_separating_zmod_forms (l : ℕ) [Fact l.Prime] (M : Type) [AddCommGroup M] [Module (ZMod l) M]
    [Finite M] : ∃ (d : ℕ) (c : Fin d → M →+ ZMod l), Nat.card M = l ^ d ∧
      ∀ x y : M, (∀ i, c i x = c i y) → x = y := by
  refine ⟨Module.finrank (ZMod l) M,
    fun i => ((Module.finBasis (ZMod l) M).coord i).toAddMonoidHom, ?_, ?_⟩
  · letI : Fintype M := Fintype.ofFinite M
    rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := ZMod l), ZMod.card]
  · intro x y h
    apply (Module.finBasis (ZMod l) M).ext_elem
    intro i
    simpa [Module.Basis.coord_apply] using h i

private theorem eq_zero_of_nsmul_eq_zero_of_coprime_torsion (l : ℕ) [Fact l.Prime] (M : Type) [AddCommGroup M]
    (htor : ∀ m : M, l • m = 0) (n : ℕ) (hn : ¬ l ∣ n) (x : M) (hx : n • x = 0) : x = 0 := by
  have hcop : Nat.Coprime n l :=
    Nat.coprime_comm.mp ((Fact.out : l.Prime).coprime_iff_not_dvd.mpr hn)
  have h := Nat.gcd_eq_gcd_ab n l
  rw [hcop.gcd_eq_one, Nat.cast_one] at h
  calc x = (1 : ℤ) • x := (one_zsmul x).symm
    _ = ((n : ℤ) * Nat.gcdA n l + (l : ℤ) * Nat.gcdB n l) • x := by rw [h]
    _ = Nat.gcdA n l • (n • x) + Nat.gcdB n l • (l • x) := by
      rw [add_smul, mul_comm (n : ℤ), mul_comm (l : ℤ), mul_smul, mul_smul, natCast_zsmul,
        natCast_zsmul]
    _ = 0 := by rw [hx, htor, smul_zero, smul_zero, add_zero]

theorem UpperTheory.V.Ws.card_cocycles_vanishing_on_inertia_le_pow :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (R M : Type) [CommRing R] [AddCommGroup M] [Module R M] [Finite M], (∀ m : M, l • m = 0) → ∀ (ρ : Representation R (G F Ω) M) (K : Subgroup (G F Ω)) (r : ℕ), ¬ l ∣ K.index → (∀ g ∈ K, ∀ m, ρ g m = m) → XRk l 1 K r → CardLe (cocOff ρ (ineOff F Ω 1 ∩ K)) (Nat.card M ^ (r + 1)) := by
  intro F Ω _ _ _ _ _ l _ R M _ _ _ _ htor ρ K r hdvd hK hX
  haveI : NeZero l := ⟨(Fact.out : l.Prime).ne_zero⟩
  have hidx : K.index ≠ 0 := fun h => hdvd (h ▸ dvd_zero l)
  haveI : K.FiniteIndex := ⟨hidx⟩
  letI : Fintype (G F Ω ⧸ K) := Fintype.ofFinite _
  have hn : ¬ l ∣ Fintype.card (G F Ω ⧸ K) := by
    rw [← Nat.card_eq_fintype_card]
    exact hdvd
  have key : ∀ w : G F Ω → M, (∀ g h, w (g * h) = w g + ρ g (w h)) → (∀ k ∈ K, w k = 0) →
      (∑ q : G F Ω ⧸ K, w q.out) = 0 → w = 0 := by
    intro w hw hwK hS
    funext h
    show w h = 0
    have e1 : ∀ q : G F Ω ⧸ K, w (h * q.out) = w (h • q).out := by
      intro q
      have hq : ((h * q.out : G F Ω) : G F Ω ⧸ K) = h • q := by
        show ((h • q.out : G F Ω) : G F Ω ⧸ K) = h • q
        rw [← MulAction.Quotient.smul_mk, QuotientGroup.out_eq']
      have hk : (h * q.out)⁻¹ * (h • q).out ∈ K :=
        QuotientGroup.eq.mp (hq.trans (QuotientGroup.out_eq' _).symm)
      have := hw (h * q.out) ((h * q.out)⁻¹ * (h • q).out)
      rw [mul_inv_cancel_left, hwK _ hk, map_zero, add_zero] at this
      exact this.symm
    have hsum : ∑ q : G F Ω ⧸ K, w (h * q.out) = ∑ q : G F Ω ⧸ K, w q.out := by
      rw [Finset.sum_congr rfl (fun q _ => e1 q)]
      exact Equiv.sum_comp (MulAction.toPerm h) (fun q : G F Ω ⧸ K => w q.out)
    have hexp : ∑ q : G F Ω ⧸ K, w (h * q.out) =
        Fintype.card (G F Ω ⧸ K) • w h + ρ h (∑ q : G F Ω ⧸ K, w q.out) := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [hw, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, map_sum]
    rw [hsum, hS, map_zero, add_zero] at hexp
    exact eq_zero_of_nsmul_eq_zero_of_coprime_torsion l M htor _ hn (w h) hexp.symm
  obtain ⟨hXfin, hXcard⟩ := hX
  obtain ⟨d, c, hM, hc⟩ := @exists_natCard_eq_pow_and_separating_zmod_forms l _ M _ (AddCommGroup.zmodModule htor) _
  have mem : ∀ z : ↥(cocOff ρ (ineOff F Ω 1 ∩ (K : Set (G F Ω)))),
      IsLocallyConstant z.1 ∧ (∀ g h, z.1 (g * h) = z.1 g + ρ g (z.1 h)) ∧
        ∀ g ∈ ineOff F Ω 1 ∩ (K : Set (G F Ω)), z.1 g = 0 := fun z => z.2
  have hone : ∀ A : ValuationSubring Ω, ¬ A.valuation ((1 : ℕ) : Ω) < 1 := by
    intro A
    simp
  have coordMem : ∀ (z : ↥(cocOff ρ (ineOff F Ω 1 ∩ (K : Set (G F Ω))))) (i : Fin d),
      (fun u : K => c i (z.1 u)) ∈ UpperTheory.V.Kum.XDual (F := F) (Ω := Ω) 1 K (ZMod l) (ZMod l) := by
    intro z i
    obtain ⟨hlc, hcoc, hvan⟩ := mem z
    have hφ : IsLocallyConstant (fun u : K => c i (z.1 u)) ∧
        (∀ a e : K, c i (z.1 ↑(a * e)) = c i (z.1 a) + c i (z.1 e)) ∧
        (∀ (A : ValuationSubring Ω) (u : K), (u : G F Ω) ∈ Ine A → c i (z.1 u) = 0) ∧
        ∀ (A : ValuationSubring Ω), A.valuation ((1 : ℕ) : Ω) < 1 → ∀ u : K, (u : G F Ω) ∈ Dec A →
          c i (z.1 u) = 0 := by
      refine ⟨?_, ?_, ?_, ?_⟩
      · exact (hlc.comp_continuous continuous_subtype_val).comp (fun m => c i m)
      · intro a e
        rw [Subgroup.coe_mul, hcoc, hK a a.2, map_add (f := _)]
      · intro A u hu
        have hin : (u : G F Ω) ∈ ineOff F Ω 1 := by
          show ∃ A, _
          exact ⟨A, hone A, hu⟩
        rw [hvan u ⟨hin, u.2⟩, map_zero]
      · intro A hA
        exact absurd hA (hone A)
    exact hφ
  let Φ : ↥(cocOff ρ (ineOff F Ω 1 ∩ (K : Set (G F Ω)))) →
      (Fin d → ↥(UpperTheory.V.Kum.XDual (F := F) (Ω := Ω) 1 K (ZMod l) (ZMod l))) × M :=
    fun z => (fun i => ⟨_, coordMem z i⟩, ∑ q : G F Ω ⧸ K, z.1 q.out)
  have hinj : Function.Injective Φ := by
    intro z z' hzz
    have h2 : (∑ q : G F Ω ⧸ K, z.1 q.out) = ∑ q : G F Ω ⧸ K, z'.1 q.out :=
      congrArg Prod.snd hzz
    have hKeq : ∀ k ∈ K, z.1 k = z'.1 k := by
      intro k hk
      exact hc _ _ (fun i => congrArg (fun p => (p.1 i).1 ⟨k, hk⟩) hzz)
    obtain ⟨_, hcoc, -⟩ := mem z
    obtain ⟨_, hcoc', -⟩ := mem z'
    have hw := key (fun g => z.1 g - z'.1 g)
      (by
        intro g h
        simp only [hcoc, hcoc', map_sub]
        abel)
      (by
        intro k hk
        simp [hKeq k hk])
      (by simp only [Finset.sum_sub_distrib, h2, sub_self])
    apply Subtype.ext
    funext g
    exact sub_eq_zero.mp (congrFun hw g)
  haveI : Finite ↥(UpperTheory.V.Kum.XDual (F := F) (Ω := Ω) 1 K (ZMod l) (ZMod l)) := hXfin
  refine (show Finite _ ∧ Nat.card _ ≤ _ from ⟨Finite.of_injective Φ hinj, ?_⟩)
  calc Nat.card ↥(cocOff ρ (ineOff F Ω 1 ∩ (K : Set (G F Ω))))
      ≤ Nat.card ((Fin d → ↥(UpperTheory.V.Kum.XDual (F := F) (Ω := Ω) 1 K (ZMod l) (ZMod l))) × M) :=
        Nat.card_le_card_of_injective Φ hinj
    _ = Nat.card ↥(UpperTheory.V.Kum.XDual (F := F) (Ω := Ω) 1 K (ZMod l) (ZMod l)) ^ d * Nat.card M := by
        rw [Nat.card_prod, Nat.card_fun, Nat.card_fin]
    _ ≤ (l ^ r) ^ d * Nat.card M :=
        Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hXcard _)
    _ = Nat.card M ^ (r + 1) := by
        rw [hM]
        ring
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Two
open scoped Classical

open scoped Pointwise in
private theorem val_smul_fix {Ω : Type} [Field Ω] [CharZero Ω] (B : ValuationSubring Ω) (v : G ℚ Ω) (x : Ω)
    (hx : v x = x) : (v • B).valuation x < 1 ↔ B.valuation x < 1 := by
  have key : ∀ A : ValuationSubring Ω, A.valuation x < 1 ↔ x = 0 ∨ x⁻¹ ∉ A := by
    intro A
    rcases eq_or_ne x 0 with h | h
    · simp [h]
    · have e := (A.valuation).one_lt_val_iff (inv_ne_zero h)
      rw [inv_inv] at e
      rw [← e, ← not_le, A.valuation_le_one_iff]
      simp [h]
  have mem : x⁻¹ ∈ v • B ↔ x⁻¹ ∈ B := by
    have hv : v x⁻¹ = x⁻¹ := by rw [map_inv₀, hx]
    constructor
    · rintro ⟨z, hz, hzx⟩
      change v z = x⁻¹ at hzx
      have hz' : z = x⁻¹ := v.injective (hzx.trans hv.symm)
      exact hz' ▸ hz
    · intro h
      exact ⟨x⁻¹, h, hv⟩
  rw [key, key, mem]

theorem UpperTheory.V.Ws.ncard_placesDividing_le_of_orbitBound :
    ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (F : IntermediateField ℚ Ω) [NumberField F] (V : Subgroup (G ℚ Ω)) (p n : ℕ), p ≠ 0 → V ≤ F.fixingSubgroup → OrbLe V p n → (plDvd F p).ncard ≤ n := by
  intro Ω _ _ _ F _ V p n hp hV hO
  obtain ⟨T, hT, hTp, hTA⟩ := hO
  have po : ∀ (w : HeightOneSpectrum (𝓞 F)) (y : 𝓞 F),
      (placeOf Ω w).valuation (algebraMap F Ω (y : F)) < 1 ↔ y ∈ w.asIdeal := by
    intro w y
    have h := isPlaceOver_placeOf Ω w
    unfold IsPlaceOver at h
    exact h y
  have fix : ∀ σ ∈ V, ∀ y : 𝓞 F, σ (algebraMap F Ω (y : F)) = algebraMap F Ω (y : F) := by
    intro σ hσ y
    exact (IntermediateField.mem_fixingSubgroup_iff F σ).1 (hV hσ) _ (by simp)
  open scoped Pointwise in
  have hup : ∀ w ∈ plDvd F p, ∃ B ∈ T, ∃ σ ∈ V, σ • B = placeOf Ω w := by
    intro w hw
    apply hTA
    have hw' : ((p : 𝓞 F)) ∈ w.asIdeal := hw
    simpa using (po w p).2 hw'
  choose! f hfT σ hσV hσ using hup
  have hinj : Set.InjOn f (plDvd F p) := by
    intro w1 h1 w2 h2 he
    apply HeightOneSpectrum.ext
    ext y
    rw [← po w1 y, ← po w2 y, ← hσ w1 h1, ← hσ w2 h2,
      val_smul_fix _ _ _ (fix _ (hσV w1 h1) y), val_smul_fix _ _ _ (fix _ (hσV w2 h2) y), he]
  calc (plDvd F p).ncard ≤ (T : Set (ValuationSubring Ω)).ncard :=
        Set.ncard_le_ncard_of_injOn f (fun w hw => hfT w hw) hinj T.finite_toSet
    _ = T.card := Set.ncard_coe_finset T
    _ ≤ n := hT
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Two
open scoped Classical

private theorem continuous_of_right_invariant_open_subgroup {Γ X : Type*} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [TopologicalSpace X] (H : Subgroup Γ) (hH : IsOpen (H : Set Γ)) (f : Γ → X)
    (hf : ∀ g, ∀ h ∈ H, f (g * h) = f g) : Continuous f := by
  refine continuous_iff_continuousAt.2 fun g => ?_
  have ht : Filter.Tendsto (fun x => g⁻¹ * x) (nhds g) (nhds 1) := by
    have := (continuous_const_mul g⁻¹).tendsto g
    simpa using this
  have hev : ∀ᶠ x in nhds g, f x = f g := by
    filter_upwards [ht (hH.mem_nhds H.one_mem)] with x hx
    have := hf g _ hx
    simpa using this
  exact tendsto_const_nhds.congr' (hev.mono fun x hx => hx.symm)

theorem UpperTheory.V.Ws.exists_descent_to_galoisGroupUnramifiedOutside :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (R M : Type) [CommRing R] [AddCommGroup M] [Module R M] [Finite M] [TopologicalSpace M] [DiscreteTopology M] (S : Finset (HeightOneSpectrum (𝓞 F))) (ρ : Representation R (G F Ω) M) (K : Subgroup (G F Ω)) (N : ℕ), (∀ v, v ∈ plDvd F N → v ∈ S) → (∀ σ ∈ ineOff F Ω N, ∀ m, ρ σ m = m) → IsOpen (K : Set (G F Ω)) → (∀ σ ∈ K, ∀ m, ρ σ m = m) → ∃ ρS : Representation R (GS Ω (S : Set (HeightOneSpectrum (𝓞 F)))) M, (∀ g m, ρS (toGS Ω _ g) m = ρ g m) ∧ ContAction ρS ∧ ∀ z ∈ cocOff ρ (ineOff F Ω N), ∃ y ∈ Z1 ρS, ∀ g, y (toGS Ω _ g) = z g := by
  intro F Ω _ _ _ _ _ R M _ _ _ _ _ _ S ρ K N hS hine hK hKρ
  have hN : ∀ v : HeightOneSpectrum (𝓞 F), v ∉ (S : Set (HeightOneSpectrum (𝓞 F))) →
      ∀ A : ValuationSubring Ω, IsPlaceOver A v → ∀ σ ∈ Inertia A, σ ∈ ineOff F Ω N := by
    intro v hv A hA σ hσ
    refine ⟨A, ?_, hσ⟩
    intro hlt
    apply hv
    apply hS
    have h1 := (hA (N : 𝓞 F)).1
    simp only [plDvd, Set.mem_setOf_eq]
    apply h1
    simpa using hlt
  have hNS : NS Ω (S : Set (HeightOneSpectrum (𝓞 F))) ≤ ρ.ker := by
    have hker : ∀ g, g ∈ ρ.ker ↔ ∀ m, ρ g m = m := by
      intro g
      rw [MonoidHom.mem_ker]
      constructor
      · intro h m
        rw [h]
        rfl
      · intro h
        exact LinearMap.ext h
    have hopen : IsOpen (ρ.ker : Set (G F Ω)) := by
      apply Subgroup.isOpen_of_mem_nhds (g := 1)
      apply Filter.mem_of_superset (hK.mem_nhds K.one_mem)
      intro σ hσ
      exact (hker σ).2 (hKρ σ hσ)
    apply Subgroup.topologicalClosure_minimal _ _ (Subgroup.isClosed_of_isOpen _ hopen)
    apply Subgroup.normalClosure_le_normal
    intro σ hσ
    simp only [Set.mem_iUnion] at hσ
    obtain ⟨v, hv, A, hA, hσ⟩ := hσ
    exact (hker σ).2 (hine σ (hN v hv A hA σ hσ))
  let ρS : Representation R (GS Ω (S : Set (HeightOneSpectrum (𝓞 F)))) M :=
    QuotientGroup.lift _ ρ hNS
  have hρS : ∀ g m, ρS (toGS Ω _ g) m = ρ g m := by
    intro g m
    rfl
  refine ⟨ρS, hρS, ?_, ?_⟩
  · show Continuous fun p : GS Ω (S : Set (HeightOneSpectrum (𝓞 F))) × M => ρS p.1 p.2
    rw [continuous_prod_of_discrete_right]
    intro m
    rw [(QuotientGroup.isQuotientMap_mk _).continuous_iff]
    apply continuous_of_right_invariant_open_subgroup K hK
    intro g h hh
    show ρ (g * h) m = ρ g m
    rw [map_mul, Module.End.mul_apply, hKρ h hh]
  · intro z hz
    obtain ⟨hzlc, hzc, hz0⟩ := hz
    have hz1 : z 1 = 0 := by
      have := hzc 1 1
      simp only [mul_one, map_one, Module.End.one_apply] at this
      simpa using this
    let φ : G F Ω →* Function.End M :=
      { toFun := fun g m => ρ g m + z g
        map_one' := by
          funext m
          show ρ 1 m + z 1 = m
          rw [hz1, map_one]
          simp
        map_mul' := by
          intro g h
          funext m
          show ρ (g * h) m + z (g * h) = ρ g (ρ h m + z h) + z g
          rw [hzc, map_mul, Module.End.mul_apply, map_add (f := _)]
          abel }
    have hkerφ : ∀ g, g ∈ φ.ker ↔ z g = 0 ∧ ∀ m, ρ g m = m := by
      intro g
      rw [MonoidHom.mem_ker]
      constructor
      · intro h
        have h' : ∀ m, ρ g m + z g = m := fun m => congrFun h m
        have h0 : z g = 0 := by simpa using h' 0
        refine ⟨h0, fun m => ?_⟩
        simpa [h0] using h' m
      · rintro ⟨h0, h1⟩
        funext m
        show ρ g m + z g = m
        rw [h0, h1, add_zero]
    have hopen : IsOpen (φ.ker : Set (G F Ω)) := by
      apply Subgroup.isOpen_of_mem_nhds (g := 1)
      have hU : z ⁻¹' {0} ∈ nhds (1 : G F Ω) :=
        (hzlc.isOpen_fiber 0).mem_nhds (by simpa using hz1)
      apply Filter.mem_of_superset (Filter.inter_mem (hK.mem_nhds K.one_mem) hU)
      rintro σ ⟨hσK, hσz⟩
      exact (hkerφ σ).2 ⟨hσz, hKρ σ hσK⟩
    have hNSφ : NS Ω (S : Set (HeightOneSpectrum (𝓞 F))) ≤ φ.ker := by
      apply Subgroup.topologicalClosure_minimal _ _ (Subgroup.isClosed_of_isOpen _ hopen)
      apply Subgroup.normalClosure_le_normal
      intro σ hσ
      simp only [Set.mem_iUnion] at hσ
      obtain ⟨v, hv, A, hA, hσ⟩ := hσ
      have hm := hN v hv A hA σ hσ
      exact (hkerφ σ).2 ⟨hz0 σ hm, hine σ hm⟩
    let φS := QuotientGroup.lift _ φ hNSφ
    let y : GS Ω (S : Set (HeightOneSpectrum (𝓞 F))) → M := fun q => φS q 0
    have hy : ∀ g, y (toGS Ω _ g) = z g := by
      intro g
      show ρ g 0 + z g = z g
      simp
    refine ⟨y, ⟨?_, ?_⟩, hy⟩
    · rw [(QuotientGroup.isQuotientMap_mk _).continuous_iff]
      have : (y ∘ QuotientGroup.mk) = z := funext hy
      rw [this]
      exact hzlc.continuous
    · intro q₁ q₂
      induction q₁ using QuotientGroup.induction_on with
      | H g =>
        induction q₂ using QuotientGroup.induction_on with
        | H h =>
          have e := hy (g * h)
          rw [map_mul] at e
          show y (toGS Ω _ g * toGS Ω _ h) = y (toGS Ω _ g) + ρS (toGS Ω _ g) (y (toGS Ω _ h))
          rw [e, hy, hy, hρS, hzc]
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Two
open scoped Classical

theorem UpperTheory.V.Ws.card_localCocycles_le_of_place_above_prime :
    LocalFiniteness → LocalTateDuality → LocalEulerChar → ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (R M : Type) [CommRing R] [AddCommGroup M] [Module R M] [Finite M], (∀ m : M, l • m = 0) → ∀ (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 F)) (ρ : Representation R (Dec (F := F) A) M), IsPlaceOver A v → ((l : ℕ) : 𝓞 F) ∈ v.asIdeal → (∀ m, IsLocallyConstant fun g => ρ g m) → CardLe (cocOff ρ ∅) (Nat.card M ^ (2 + locDeg v)) := by
  intro hF hT hE F Ω _ _ _ _ _ l _ R M _ _ _ _ hl A v ρ hA hv hρ
  obtain ⟨inst, ρ', hρ'⟩ := exists_zmod_prime_representation_of_torsion l (Dec (F := F) A) R M hl ρ
  letI : TopologicalSpace M := ⊥
  haveI : DiscreteTopology M := ⟨rfl⟩
  have hc : ReciprocityTheory.Gal.ContAction ρ' := by
    unfold ReciprocityTheory.Gal.ContAction
    rw [continuous_prod_of_discrete_right]
    intro m
    simp only [hρ']
    exact (hρ m).continuous
  obtain ⟨f1, h1⟩ := local_h1_finite_mod_l hF hT hE F Ω l M A v ρ' hA hc
  obtain ⟨fz, hz⟩ := cocycle_card_euler_formula _ _ M ρ' hc f1
  rw [if_pos hv] at h1
  have h0 : 0 < Nat.card (H0 ρ') := by
    haveI : Finite (H0 ρ') := Subtype.finite
    haveI : Nonempty (H0 ρ') := ⟨0⟩
    exact Nat.card_pos
  have hZ : CardLe (Z1 ρ') (Nat.card M ^ (2 + locDeg v)) := by
    refine ⟨fz, Nat.le_of_mul_le_mul_right ?_ h0⟩
    rw [hz]
    calc Nat.card (H1 ρ') * Nat.card M
        ≤ Nat.card (H0 ρ') * Nat.card M ^ (1 + locDeg v) * Nat.card M := Nat.mul_le_mul_right _ h1
      _ = Nat.card M ^ (2 + locDeg v) * Nat.card (H0 ρ') := by ring
  have hmem : ∀ z : cocOff ρ ∅, z.1 ∈ Z1 ρ' := fun z =>
    (mem_Z1_iff_cocycle ρ' _).2 ⟨z.2.1.continuous, fun g h => by rw [hρ']; exact z.2.2.1 g h⟩
  exact hZ.of_injective (fun z => ⟨z.1, hmem z⟩) fun a b h => Subtype.ext (congrArg (fun z : Z1 ρ' => z.1) h)
end
