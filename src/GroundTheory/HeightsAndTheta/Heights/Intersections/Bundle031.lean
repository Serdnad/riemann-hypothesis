module

public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle026
public import Mathlib.FieldTheory.Relrank
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle027
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle001
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle023
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle017
import Mathlib.Algebra.AffineMonoid.Basic
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
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle006

@[expose] public section

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 IndefiniteRowSideFullHecke.Inter

def SemilocRank.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (κ : K → K') (v : (Σ k, ι k) → (Σ k', ι' k')) (P' : Ideal (MRing ι')) (n : ℕ)
    (G : GenFibre v P') (J : IFamily G.Φ (fibreIdx ι' κ)) (s : MRing ι) (α : K → ℕ)
    (W : Ideal (MRing ι)) (hv : IsBlockMap κ v) (hP' : IsArithVar P' (n + 1)),
    IsArithVar (imageZ v P') (n + 1) → IsFieldIntersection J → IsMultiHomog s α → s ∉ imageZ v P' →
    W ∈ divSupp (imageZ v P') s →
    haveI := hP'.2.1.1
    letI := (locToSemiloc hv P' W).toAlgebra
    (Module.finrank (locRing (imageZ v P') W) (semiLocRing P' (fibreOver v P' W)) : ℤ) =
      J (fibreIdeal κ G) 0 Fin.elim0

end GroundTheory.Heights₂.Heights.Inter
end
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 IndefiniteRowSideFullHecke.Inter

def SemilocRankAdjoin.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (κ : K → K') (v : (Σ k, ι k) → (Σ k', ι' k')) (P' : Ideal (MRing ι')) (n : ℕ)
    (G : GenFibre v P') (s : MRing ι) (α : K → ℕ) (W : Ideal (MRing ι)) (i' : ∀ k', ι' k')
    (hv : IsBlockMap κ v) (hP' : IsArithVar P' (n + 1)),
    IsArithVar (imageZ v P') (n + 1) → IsMultiHomog s α → s ∉ imageZ v P' →
    W ∈ divSupp (imageZ v P') s → (∀ k', (X ⟨k', i' k'⟩ : MRing ι') ∉ P') →
    haveI := hP'.2.1.1
    letI := (locToSemiloc hv P' W).toAlgebra
    Module.finrank (locRing (imageZ v P') W) (semiLocRing P' (fibreOver v P' W)) =
      Module.finrank G.Φ (IntermediateField.adjoin G.Φ
        (Set.range fun q : Σ k : FibreBlock κ, ι' k.1 => G.x' ⟨q.1.1, q.2⟩ / G.x' ⟨q.1.1, i' q.1.1⟩))

end GroundTheory.Heights₂.Heights.Inter
end
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 IndefiniteRowSideFullHecke.Inter

def SemilocRankFrac.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (κ : K → K') (v : (Σ k, ι k) → (Σ k', ι' k')) (P' : Ideal (MRing ι')) (n : ℕ)
    (G : GenFibre v P') (s : MRing ι) (α : K → ℕ) (W : Ideal (MRing ι)) (i' : ∀ k', ι' k')
    (hv : IsBlockMap κ v) (hP' : IsArithVar P' (n + 1)) [Algebra ℚ G.Φ'],
    IsArithVar (imageZ v P') (n + 1) → IsMultiHomog s α → s ∉ imageZ v P' →
    W ∈ divSupp (imageZ v P') s → (∀ k', (X ⟨k', i' k'⟩ : MRing ι') ∉ P') →
    haveI := hP'.2.1.1
    letI := (locToSemiloc hv P' W).toAlgebra
    Module.finrank (locRing (imageZ v P') W) (semiLocRing P' (fibreOver v P' W)) =
      IntermediateField.relfinrank
        (IntermediateField.adjoin ℚ
          (Set.range ((fun q : Σ k', ι' k' => G.x' q / G.x' ⟨q.1, i' q.1⟩) ∘ v)))
        (IntermediateField.adjoin ℚ (Set.range fun q : Σ k', ι' k' => G.x' q / G.x' ⟨q.1, i' q.1⟩))

end GroundTheory.Heights₂.Heights.Inter
end
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section


set_option maxHeartbeats 1000000 in
theorem RegularityLocal.proof (hO : RegularityOrder.Statement) (hE : RegularityMaximalSpectrum.Statement) :
    RegularityLocal.Statement := by
  classical
  intro K _ ι _ P b hP hb
  have : P.IsPrime := hP.2.1.1
  obtain ⟨e, he⟩ := hE K ι P hP
  obtain ⟨hfree, hfinite, -⟩ := hO K ι P hP
  let φ : regRing P →+* FractionRing (MRing ι ⧸ P) := (funField P).subtype.comp (regRing P).subtype
  have hφ : Function.Injective φ := Subtype.val_injective.comp Subtype.val_injective
  let ψ : ∀ W : {W : Ideal (MRing ι) // IsClosedPt W ∧ P ≤ W}, regRing P →+* locRing P W.1 :=
    fun W => φ.codRestrict (locRing P W.1) fun x => x.2 W.1 W.2.1 W.2.2
  have hcard : ∀ W : {W : Ideal (MRing ι) // IsClosedPt W ∧ P ≤ W},
      locIdeal P W.1 (φ b) = Ideal.span {ψ W b} := fun W => locIdeal_eq_span (b.2 W.1 W.2.1 W.2.2)
  have hloc : ∀ W, @IsLocalization (regRing P) _ (e W).asIdeal.primeCompl (locRing P W.1) _ (ψ W).toAlgebra :=
    fun W => by
      let _ := (ψ W).toAlgebra
      have := (e W).isMaximal
      have hL : ∀ x : regRing P, ((algebraMap (regRing P) (locRing P W.1) x : locRing P W.1) : FractionRing (MRing ι ⧸ P)) = φ x := fun _ => rfl
      refine (isLocalization_iff (e W).asIdeal.primeCompl (locRing P W.1)).2 ⟨?_, ?_, ?_⟩
      · rintro ⟨s, hs⟩
        have hs0 : φ s ≠ 0 := fun h0 => hs (by rw [(map_eq_zero_iff φ hφ).1 h0]; exact (e W).asIdeal.zero_mem)
        refine IsUnit.of_mul_eq_one ⟨(φ s)⁻¹, (he W _).2 ⟨1, s, hs, by change (φ s)⁻¹ * φ s = φ 1; rw [map_one, inv_mul_cancel₀ hs0]⟩⟩ ?_
        apply Subtype.ext
        simp only [Subring.coe_mul, hL, Subring.coe_one]
        exact mul_inv_cancel₀ hs0
      · intro z
        obtain ⟨x, s, hs, hxs⟩ := (he W z).1 z.2
        change (z : FractionRing (MRing ι ⧸ P)) * φ s = φ x at hxs
        exact ⟨⟨x, ⟨s, hs⟩⟩, Subtype.ext (by simp only [Subring.coe_mul, hL]; exact hxs)⟩
      · intro x y hxy
        have h1 := congrArg Subtype.val hxy
        rw [hL, hL] at h1
        exact ⟨1, by rw [hφ h1]⟩

  have hone : ∀ W : {W : Ideal (MRing ι) // IsClosedPt W ∧ P ≤ W}, b ∉ (e W).asIdeal →
      Nat.card (locRing P W.1 ⧸ locIdeal P W.1 (φ b)) = 1 := fun W hbW => by
    let _ := (ψ W).toAlgebra
    have := hloc W
    have hu : IsUnit (ψ W b) :=
      IsLocalization.map_units (M := (e W).asIdeal.primeCompl) (locRing P W.1) ⟨b, hbW⟩
    rw [hcard, Ideal.span_singleton_eq_top.2 hu]
    exact Nat.card_eq_one_iff_unique.2 ⟨Ideal.Quotient.subsingleton_iff.2 rfl, ⟨0⟩⟩

  set I : Ideal (regRing P) := Ideal.span {b} with hI
  have : Finite (regRing P ⧸ I) :=
    Ideal.finiteQuotientOfFreeOfNeBot I (by rwa [hI, Ne, Ideal.span_singleton_eq_bot])
  have : Fintype (PrimeSpectrum (regRing P ⧸ I)) := by
    set_option synthInstance.maxHeartbeats 200000 in
      exact Fintype.ofFinite _
  let m : PrimeSpectrum (regRing P ⧸ I) → MaximalSpectrum (regRing P) := fun p =>
    ⟨p.asIdeal.comap (Ideal.Quotient.mk I),
      Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective (K := p.asIdeal)⟩
  let g : PrimeSpectrum (regRing P ⧸ I) → {W : Ideal (MRing ι) // IsClosedPt W ∧ P ≤ W} := fun p => e.symm (m p)
  have heg : ∀ p, (e (g p)).asIdeal = p.asIdeal.comap (Ideal.Quotient.mk I) := fun p =>
    congrArg MaximalSpectrum.asIdeal (e.apply_symm_apply (m p))
  have hg : Function.Injective g := fun p q hpq => by
    have h1 := congrArg (fun W => (e W).asIdeal) hpq
    simp only [heg] at h1
    exact PrimeSpectrum.ext (Ideal.comap_injective_of_surjective _ Ideal.Quotient.mk_surjective h1)
  clear_value g m

  have hgp : ∀ p : PrimeSpectrum (regRing P ⧸ I),
      Nat.card (locRing P (g p).1 ⧸ locIdeal P (g p).1 (φ b)) = Nat.card (Localization.AtPrime p.asIdeal) :=
    fun p => by
      have := (e (g p)).isMaximal
      rw [hcard]
      exact card_quot_span_eq_card_localization (ψ (g p)) b (e (g p)).asIdeal p.asIdeal (heg p) (hloc (g p))

  have hsupp : ∀ W : {W : Ideal (MRing ι) // IsClosedPt W ∧ P ≤ W}, b ∈ (e W).asIdeal → ∃ p, g p = W :=
    fun W hbW => by
      have := (e W).isMaximal
      have hker : RingHom.ker (Ideal.Quotient.mk I) ≤ (e W).asIdeal := by
        rw [Ideal.mk_ker, hI, Ideal.span_le, Set.singleton_subset_iff]
        exact hbW
      refine ⟨⟨(e W).asIdeal.map (Ideal.Quotient.mk I),
        Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective hker⟩, ?_⟩
      apply e.injective
      apply MaximalSpectrum.ext
      rw [heg, Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, sup_eq_left,
        ← RingHom.ker_eq_comap_bot]
      exact hker
  have hfin : {W : Ideal (MRing ι) | IsClosedPt W ∧ P ≤ W ∧ Nat.card (locRing P W ⧸ locIdeal P W (φ b)) ≠ 1} ⊆
      Set.range (fun p => (g p).1) := by
    rintro W ⟨h1, h2, h3⟩
    obtain ⟨p, hp⟩ := hsupp ⟨W, h1, h2⟩ (by_contra fun hn => h3 (hone ⟨W, h1, h2⟩ hn))
    exact ⟨p, congrArg Subtype.val hp⟩
  refine ⟨(Set.finite_range _).subset hfin, ?_⟩

  refine (finsum_mem_eq_sum_of_injective {W : Ideal (MRing ι) | IsClosedPt W ∧ P ≤ W}
    (fun W => Real.log (Nat.card (locRing P W ⧸ locIdeal P W (φ b)))) (fun p => (g p).1)
    (Subtype.val_injective.comp hg) (fun p => (g p).2)
    fun W hW h0 => hfin ⟨hW.1, hW.2, fun h1 => h0 (by rw [h1, Nat.cast_one, Real.log_one])⟩).trans ?_
  rw [log_card_eq_sum_log_card_localization (regRing P ⧸ I)]
  exact Finset.sum_congr rfl fun p _ => congrArg (fun n : ℕ => Real.log n) (hgp p)

end

end GroundTheory.Heights₂.Heights.Inter
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo NumberField

noncomputable section

theorem RegularityOrder.order_of_integral {F : Type*} [Field F] [NumberField F] (S : Subring F)
    (hint : ∀ x ∈ S, IsIntegral ℤ x) (hden : ∀ x : F, ∃ c ∈ S, c ≠ 0 ∧ x * c ∈ S) :
    Module.Finite ℤ S ∧ Module.Free ℤ S ∧ Module.finrank ℤ S = Module.finrank ℚ F := by

  have hmul : ∀ x : F, ∃ m : ℤ, m ≠ 0 ∧ (m : F) * x ∈ S := by
    intro x
    obtain ⟨c, hc, hc0, hxc⟩ := hden x
    have hci : IsIntegral ℤ (⟨c, hc⟩ : S) :=
      (isIntegral_algHom_iff S.subtype.toIntAlgHom Subtype.val_injective).1 (hint c hc)
    have hne := Ideal.comap_ne_bot_of_integral_mem (I := Ideal.span {(⟨c, hc⟩ : S)})
      (fun h => hc0 (congrArg Subtype.val h)) (Ideal.mem_span_singleton_self _) hci
    obtain ⟨m, hm, hm0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    obtain ⟨d, hd⟩ := Ideal.mem_span_singleton'.1 (Ideal.mem_comap.1 hm)
    refine ⟨m, hm0, ?_⟩
    have hmdc : (m : F) = (d : F) * c := by
      have := congrArg Subtype.val hd
      simpa using this.symm
    rw [hmdc, mul_assoc, mul_comm c x]
    exact S.mul_mem d.2 hxc

  let φ : S →ₗ[ℤ] 𝓞 F :=
    { toFun := fun x => ⟨x, hint x x.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hφ : Function.Injective φ := fun x y h =>
    Subtype.ext (congrArg (fun z : 𝓞 F => (z : F)) h)
  have : Module.Finite ℤ S := Module.Finite.of_injective φ hφ
  have : Module.IsTorsionFree ℤ S := hφ.moduleIsTorsionFree φ (fun r x => φ.map_smul r x)
  have : Module.Free ℤ S := Module.free_of_finite_type_torsion_free'
  refine ⟨inferInstance, inferInstance, le_antisymm ?_ ?_⟩
  · rw [← RingOfIntegers.rank]
    exact LinearMap.finrank_le_finrank_of_injective hφ
  · rw [← RingOfIntegers.rank]
    obtain ⟨n, s, hs⟩ := Module.Finite.exists_fin (R := ℤ) (M := 𝓞 F)
    choose m hm0 hmS using fun i => hmul (s i : F)
    have hM0 : (∏ i, m i) ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ => hm0 i
    have hMS : ∀ y : 𝓞 F, ((∏ i, m i : ℤ) : F) * y ∈ S := by
      intro y
      have hy : y ∈ Submodule.span ℤ (Set.range s) := hs ▸ Submodule.mem_top
      induction hy using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨i, rfl⟩ := hy
        obtain ⟨q, hq⟩ : m i ∣ ∏ j, m j := Finset.dvd_prod_of_mem m (Finset.mem_univ i)
        rw [hq, Int.cast_mul, mul_comm (m i : F), mul_assoc]
        exact S.mul_mem (intCast_mem S q) (hmS i)
      | zero => simp
      | add y z _ _ hy hz =>
        convert S.add_mem hy hz using 1
        push_cast
        ring
      | smul r y _ hy =>
        convert S.zsmul_mem hy r using 1
        simp only [RingOfIntegers.coe_eq_algebraMap, zsmul_eq_mul, map_mul, map_intCast]
        ring
    let ψ : 𝓞 F →ₗ[ℤ] S :=
      { toFun := fun y => ⟨((∏ i, m i : ℤ) : F) * y, hMS y⟩
        map_add' := fun y z => Subtype.ext (by push_cast; ring)
        map_smul' := fun r y => Subtype.ext (by
          simp only [RingOfIntegers.coe_eq_algebraMap, zsmul_eq_mul, map_mul, map_intCast,
            Subring.coe_mul, SubringClass.coe_intCast, RingHom.id_apply]
          ring) }
    have hψ : Function.Injective ψ := by
      intro y z h
      have h' : ((∏ i, m i : ℤ) : F) * y = ((∏ i, m i : ℤ) : F) * z := congrArg Subtype.val h
      exact RingOfIntegers.eq_iff.1 (mul_left_cancel₀ (Int.cast_ne_zero.2 hM0) h')
    exact LinearMap.finrank_le_finrank_of_injective hψ

theorem RegularityOrder.proof (h₁ : RegularityFunctionFieldNumber.Statement) (h₂ : RegularityDenominator.Statement)
    (h₃ : RegularityIntegral.Statement) : RegularityOrder.Statement := by
  intro K _ ι _ P hP
  let f : funField P →ₐ[ℤ] FractionRing (MRing ι ⧸ P) :=
    { (funField P).subtype with commutes' := fun r => by simp }
  have hint₀ : ∀ x ∈ regRing P, IsIntegral ℤ x := fun x hx =>
    (isIntegral_algHom_iff f Subtype.val_injective).1 (h₃ K ι P hP ⟨x, hx⟩)
  obtain ⟨hF, hN⟩ := h₁ K ι P hP
  let _ : Field (funField P) := hF.toField
  have := hN
  have hint : ∀ x ∈ regRing P, IsIntegral ℤ x := hint₀
  have hden : ∀ x : funField P, ∃ c ∈ regRing P, c ≠ 0 ∧ x * c ∈ regRing P := by
    intro x
    obtain ⟨c, hc0, hc⟩ := h₂ K ι P x hP
    exact ⟨c, fun W h1 h2 => (hc W h1 h2).1, hc0, fun W h1 h2 => (hc W h1 h2).2⟩
  obtain ⟨hfin, hfree, hrank⟩ := RegularityOrder.order_of_integral (F := funField P) (regRing P) hint hden
  exact ⟨hfree, hfin, fun _ _ => hrank⟩

end

end GroundTheory.Heights₂.Heights.Inter
end
