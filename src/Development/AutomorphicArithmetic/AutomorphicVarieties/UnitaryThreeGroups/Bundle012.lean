module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
public import Mathlib.RingTheory.AdicCompletion.Noetherian
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import ReciprocityTheory.GaloisValuations.Global
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.Bundle001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.GaloisCohomologyLength.Bundle002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.DecGen
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle057
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle010
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisCochains.Bundle001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.ConjStableShaFam
public import Mathlib.NumberTheory.NumberField.Discriminant.Defs
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsIsKroneckerCharOfDiscr
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.ClassFieldRamification.Bundle002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.Rigid0
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Bundle007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.Bundle009
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Topology.Algebra.ClopenNhdofOne
import Mathlib.Topology.Connected.Separation
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.DirichletPrimeToLPartMulLPowerPart
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.UnitaryThreeReflectionRight

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Matrix IsLocalRing
open UpperTheory.V UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.Alg UpperTheory.V.U3

open Formalism.GaloisCohomology in
theorem UpperTheory.exists_decompositionField_frobenius_data :
    ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 ℚ)), IsPlaceOver A v →
          CompactSpace (Dec (F := ℚ) A) ∧ ((Ine (F := ℚ) A).subgroupOf (Dec (F := ℚ) A)).Normal ∧ IsClosed (Ine (F := ℚ) A : Set (G ℚ Ω)) ∧
          (∃ fr : Dec (F := ℚ) A, ((Ine (F := ℚ) A).subgroupOf (Dec (F := ℚ) A) ⊔ Subgroup.zpowers fr).topologicalClosure = ⊤) ∧
          ∀ n : ℕ, 0 < n → ∃ U : Subgroup (Dec (F := ℚ) A), IsOpen (U : Set (Dec (F := ℚ) A)) ∧ (Ine (F := ℚ) A).subgroupOf (Dec (F := ℚ) A) ≤ U ∧ U.index = n := by
  intro Ω _ _ _ A v hv
  haveI : IsGalois ℚ Ω := {}
  obtain ⟨φ, -, h1, h2⟩ := UpperTheory.V.GC.decZhat ℚ Ω v A hv
  refine ⟨isCompact_iff_compactSpace.1 (isClosed_Dec A).isCompact, inferInstance, isClosed_Ine A, ⟨φ, h1⟩,
    fun n hn => ?_⟩
  obtain ⟨d, hd, hI, hφ⟩ := h2 n hn
  haveI : NeZero n := ⟨hn.ne'⟩
  refine ⟨d.ker, hd {1}, fun s hs => hI s hs, ?_⟩
  have hs : d.range = ⊤ := by
    rw [eq_top_iff]
    intro x _
    refine ⟨φ ^ (Multiplicative.toAdd x).val, ?_⟩
    rw [map_pow, hφ, ← ofAdd_nsmul, nsmul_eq_mul, mul_one, ZMod.natCast_zmod_val, ofAdd_toAdd]
  rw [Subgroup.index_ker, hs, Subgroup.card_top, Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]
end

section

open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V UpperTheory.V.Base

private theorem UpperTheory.exists_fixed_square_root_odd {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosed Ω] (g : Ω →+* Ω) (n : ℕ) :
    Odd n → (∀ ζ : Ω, ζ ^ n = 1 → g ζ = ζ) →
      ∃ m : ℤ, m.natAbs = n ∧ m % 4 = 1 ∧ ∃ s : Ω, s ^ 2 = m ∧ g s = s := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn hg
    by_cases h1 : n = 1
    · subst h1
      exact ⟨1, rfl, rfl, 1, by norm_num, map_one g⟩
    · set p := n.minFac with hp_def
      have hp : p.Prime := Nat.minFac_prime h1
      obtain ⟨k, hk⟩ := Nat.minFac_dvd n
      rw [← hp_def] at hk
      have hp2 : p ≠ 2 := by
        intro h2
        rw [h2] at hk
        obtain ⟨a, ha⟩ := hn
        omega
      have hkpos : 0 < k := by
        rcases Nat.eq_zero_or_pos k with h | h
        · obtain ⟨a, ha⟩ := hn
          rw [h, mul_zero] at hk
          omega
        · exact h
      have hkn : k < n := by
        rw [hk]
        have := hp.two_le
        nlinarith
      have hkodd : Odd k := (Nat.odd_mul.mp (hk ▸ hn)).2
      obtain ⟨m', hm'abs, hm'4, s', hs'sq, hgs'⟩ :=
        ih k hkn hkodd (fun ζ hζ => hg ζ (by rw [hk, pow_mul', hζ, one_pow]))
      haveI : Fact p.Prime := ⟨hp⟩
      haveI : NeZero (p : Ω) := ⟨Nat.cast_ne_zero.mpr hp.ne_zero⟩
      obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω p
      obtain ⟨⟨x, hx⟩, hall⟩ := CF.gauss Ω p ζ hp2 hζ
      have hgz : g ζ = ζ ^ 1 := by
        rw [pow_one]
        exact hg ζ (by rw [hk, pow_mul, hζ.pow_eq_one, one_pow])
      have hgx : g x = x := by
        have := (hall x hx).2 g 1 hgz
        simpa [legendreSym.at_one] using this
      have hps : (CF.pStar p).natAbs = p := by
        simp [CF.pStar, Int.natAbs_mul, Int.natAbs_pow]
      have hp4 : CF.pStar p % 4 = 1 := by
        obtain ⟨a, ha⟩ := hp.odd_of_ne_two hp2
        clear_value p
        rcases Nat.even_or_odd a with ⟨c, hc⟩ | ⟨c, hc⟩
        · have e : p / 2 = 2 * c := by omega
          have hpz : (p : ℤ) = 4 * c + 1 := by omega
          rw [CF.pStar, e, pow_mul, neg_one_sq, one_pow, one_mul, hpz]
          omega
        · have e : p / 2 = 2 * c + 1 := by omega
          have hpz : (p : ℤ) = 4 * c + 3 := by omega
          rw [CF.pStar, e, pow_succ, pow_mul, neg_one_sq, one_pow, one_mul, hpz]
          omega
      refine ⟨CF.pStar p * m', ?_, ?_, x * s', ?_, ?_⟩
      · rw [Int.natAbs_mul, hps, hm'abs, hk]
      · rw [Int.mul_emod, hp4, hm'4]
        rfl
      · rw [mul_pow, hx, hs'sq]
        push_cast
        ring
      · rw [map_mul, hgx, hgs']

theorem UpperTheory.mem_galOf_quadratic_of_fixes_discr_roots_of_unity :
    ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (K : Type) [Field K] [NumberField K] [Algebra K Ω], Module.finrank ℚ K = 2 → Odd (discr K).natAbs → ∀ g : G ℚ Ω, (∀ ζ : Ω, ζ ^ (discr K).natAbs = 1 → g ζ = ζ) → g ∈ galOf ℚ K Ω := by
  intro Ω _ _ _ K _ _ _ hK hodd g hg
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  obtain ⟨m, hmabs, hm4, s, hs, hgs⟩ :=
    UpperTheory.exists_fixed_square_root_odd (g : Ω →+* Ω) (discr K).natAbs hodd (fun ζ h => by simpa using hg ζ h)
  have hd4 : discr K % 4 = 1 := by
    have h2 : Odd (discr K) := Int.natAbs_odd.mp hodd
    rcases GlobalTheory.QuadraticZeta.discr_mod_four hK with h | h
    · obtain ⟨c, hc⟩ := h2
      omega
    · exact h
  have hm : m = discr K := by
    rcases Int.natAbs_eq_natAbs_iff.mp hmabs with h | h
    · exact h
    · rw [h] at hm4
      omega
  subst hm
  have hgs' : g s = s := by simpa using hgs
  obtain ⟨b, t, n, hb0, hb1, hd⟩ := GlobalTheory.QuadraticZeta.exists_basis hK
  set θ : Ω := algebraMap K Ω ((b 1 : 𝓞 K) : K) with hθ
  have hθ2 : θ ^ 2 = t * θ - n := by
    have := congrArg (fun z : 𝓞 K => algebraMap K Ω (z : K)) hb1
    simpa [hθ] using this
  have hy : (2 * θ - t) ^ 2 = s ^ 2 := by
    rw [hs, hd]
    push_cast
    linear_combination 4 * hθ2
  have hgθ : g θ = θ := by
    have hgy : g (2 * θ - t) = 2 * θ - t := by
      rcases sq_eq_sq_iff_eq_or_eq_neg.mp hy with h | h
      · rw [h, hgs']
      · rw [h, map_neg, hgs']
    have e : 2 * g θ - t = 2 * θ - t := by
      rw [← hgy, map_sub, map_mul, map_ofNat, map_intCast]
    linear_combination (1 / 2 : Ω) * e
  have hint : ∀ a : 𝓞 K, g (algebraMap K Ω (a : K)) = algebraMap K Ω (a : K) := by
    intro a
    have e : algebraMap K Ω (a : K) = ((b.repr a 0 : ℤ) : Ω) + ((b.repr a 1 : ℤ) : Ω) * θ := by
      conv_lhs => rw [GlobalTheory.QuadraticZeta.eq_coord b hb0 a]
      simp [hθ]
    rw [e, map_add (f := _), map_mul, map_intCast, map_intCast, hgθ]
  change ∀ x : K, g (algebraMap K Ω x) = algebraMap K Ω x
  intro x
  obtain ⟨a, c, hc, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 K) x
  rw [map_div₀, map_div₀]
  exact congrArg₂ (· / ·) (hint a) (hint c)
end

section

open Matrix IsLocalRing UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.HV

private theorem norm_lt_one_of_nonunit {l : ℕ} [Fact l.Prime] (c : Coef l) (b : c.O) (hb : ¬ IsUnit b) :
    ‖(b : PadicAlgCl l)‖ < 1 := by
  classical
  haveI := c.dvr
  haveI := c.fin
  by_cases h0 : b = 0
  · subst h0
    simp
  have key := UpperTheory.V.Base.normO l c.O b h0
  have hv0 : IsDiscreteValuationRing.addVal c.O b ≠ 0 := fun h =>
    hb ((IsDiscreteValuationRing.addVal_eq_zero_iff).1 h)
  have hvt : IsDiscreteValuationRing.addVal c.O b ≠ ⊤ := fun h =>
    h0 ((IsDiscreteValuationRing.addVal_eq_top_iff).1 h)
  have hn : (IsDiscreteValuationRing.addVal c.O b).toNat ≠ 0 := by
    intro h
    rw [ENat.toNat_eq_zero] at h
    tauto
  have hl : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have hr : ((l : ℝ)⁻¹) ^ (IsDiscreteValuationRing.addVal c.O b).toNat < 1 :=
    pow_lt_one₀ (by positivity) (inv_lt_one_of_one_lt₀ hl) hn
  rw [← key] at hr
  by_cases he : (UpperTheory.V.Base.eO l c.O).toNat = 0
  · rw [he, pow_zero] at hr
    exact absurd hr (lt_irrefl 1)
  · exact (pow_lt_one_iff_of_nonneg (norm_nonneg _) he).1 hr

private theorem isLocPt_toBar {l : ℕ} [Fact l.Prime] {c : Coef l} {R : Type} [CommRing R] [Algebra c.O R]
    [IsCO c.O R] (x : R →ₐ[c.O] c.O) : IsLocPt (toBar x) := by
  intro y hy
  refine norm_lt_one_of_nonunit c (x y) fun hu => ?_
  have h2 : IsUnit (y - algebraMap c.O R (x y)) := by
    by_contra hn
    have h3 : y - algebraMap c.O R (x y) ∈ maximalIdeal R := hn
    have h4 : algebraMap c.O R (x y) ∈ maximalIdeal R := by simpa using Ideal.sub_mem _ hy h3
    exact h4 (hu.map _)
  have h5 := h2.map x
  rw [map_sub, AlgHom.commutes] at h5
  simp at h5

private theorem hom_ext_gr {O A K : Type} [CommRing O] [CommRing A] [Algebra O A] (𝒜 : ℤ → Submodule O A)
    [GradedAlgebra 𝒜] [CommRing K] [Algebra O K] (ξ ξ' : A →ₐ[O] K) (h : ∀ j, ∀ f ∈ 𝒜 j, ξ f = ξ' f) : ξ = ξ' := by
  refine AlgHom.ext fun f => ?_
  induction f using DirectSum.Decomposition.inductionOn 𝒜 with
  | zero => simp
  | homogeneous m => exact h _ _ m.2
  | add a b ha hb => rw [map_add (f := _), map_add (f := _), ha, hb]

theorem UpperTheory.V.U3.gradedModel_pointCondition_of_ptHyp :
    ∀ {l : ℕ} [Fact l.Prime] {c : Coef l} {Γ H : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
      {η : Γ →* ℤˣ} {Ψ : Γ →* (c.O)ˣ} {N : Set Γ} {ι : H →* Γ} {hι : Continuous ι}
      {U : Univ (GCond.noCondition c.O (η.comp ι) (Ψ.comp ι))} {I : Ideal U.R} {cc g₁ : Γ} (S : SRing N hι U I cc g₁) (M : Model S (PadicAlgCl l)), l ≠ 2 → Marks η Ψ cc g₁ →
      M2 M.𝒜 M.Q.ideal → PtHyp η S.r.hom M.x₀ → M3 M.𝒜 (PadicAlgCl l) M.x M.Q.ideal := by
  intro l _ c Γ H _ _ _ _ _ _ η Ψ N ι hι U I cc g₁ S M hl hm h2 hpt
  intro x₁ hS hN hP hne
  exfalso
  apply hne
  obtain ⟨t, f, hf, hact⟩ := M.pts h2 x₁ hS
  have sg := model_signs S M hl hm f hf
  have hN' : NegZero M.𝒜 (f.comp M.q) := by
    intro j hj a ha
    rw [← hact, act_of_mem _ _ _ ha, hN j hj a ha, mul_zero]
  have hP' : PosZero M.𝒜 (f.comp M.q) := by
    intro j hj a ha
    rw [← hact, act_of_mem _ _ _ ha, hP j hj a ha, mul_zero]
  have hfix := hpt.fixed f hf (sg.1.1 hN') (sg.2.1.1 hP')
  have hb : IsLocPt (toBar M.x₀) := isLocPt_toBar M.x₀
  have hconj : push (toBar M.x₀) S.r.hom = conjBy ((tor (PadicAlgCl l)) 1) (push f S.r.hom) := by
    rw [hfix]
    ext g : 1
    simp [conjBy]
  have heq := sg.2.2 (toBar M.x₀) hb 1 hconj
  apply hom_ext_gr M.𝒜
  intro j a ha
  by_cases hj : j = 0
  · subst hj
    have e1 := congrArg (fun φ => φ a) hact
    have e2 := congrArg (fun φ => φ a) heq
    simp only [act_of_mem _ _ _ ha] at e1 e2
    simp at e1 e2
    rw [← M.x₀_q]
    simp
    rw [e1, e2]
  · rcases lt_or_gt_of_ne hj with h | h
    · rw [hN j h a ha, AlgHom.comp_apply, M.wring.fixed j hj a ha, map_zero]
    · rw [hP j h a ha, AlgHom.comp_apply, M.wring.fixed j hj a ha, map_zero]
end
