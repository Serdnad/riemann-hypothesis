module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.RatTorsionFree
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisCochains.GLinkQuot
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Bundle008
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Bundle007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.ClassFieldRamification.Bundle002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.ClassFieldRamification.Bundle001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.Bundle001
import Mathlib.Algebra.Module.StablyFree.Basic
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle010
public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.SlopeTestRemainingChoices
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.ContinuousResP
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.ScNorm
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.Radical.NatInt
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
import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.IsUnitOrIsUnitOfAddOne
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.ContinuousCoboundaries2

@[expose] public section

section

open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Pr UpperTheory.V.Fr UpperTheory.V

theorem UpperTheory.V.Fr.clrk_tr :
    ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (F : Type) [Field F] [NumberField F] [Algebra F Ω] (U : Subgroup (G ℚ Ω)), U ≤ galOf ℚ F Ω → GC.clRk l (U.comap (galEmb ℚ F Ω)) = GC.clRk l U := by
  intro Ω _ _ _ l _ F _ _ _ U hU
  haveI : Module.IsTorsionFree F Ω := DivisionSemiring.to_moduleIsTorsionFree
  haveI : IsAlgClosure F Ω := ⟨IsAlgClosure.isAlgClosed ℚ, Algebra.IsAlgebraic.tower_top (K := ℚ) F⟩
  have hemb := (galEmbTop ℚ F Ω).1
  have hfam := (galEmbFam ℚ F Ω l).1
  let e : U.comap (galEmb ℚ F Ω) ≃ U :=
    { toFun := fun u => ⟨galEmb ℚ F Ω u.1, u.2⟩
      invFun := fun u => ⟨Kum.toGal F hU u, u.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hc : Continuous e := (hemb.continuous.comp continuous_subtype_val).subtype_mk _
  have hc' : Continuous e.symm := (hemb.continuous_iff.2 continuous_subtype_val).subtype_mk _
  have hI : ∀ (A : ValuationSubring Ω) (σ : G F Ω), galEmb ℚ F Ω σ ∈ Ine (F := ℚ) A ↔ σ ∈ Ine (F := F) A :=
    fun A σ => SetLike.ext_iff.1 (hfam A).2 σ
  have hD : ∀ (A : ValuationSubring Ω) (σ : G F Ω), galEmb ℚ F Ω σ ∈ Dec (F := ℚ) A ↔ σ ∈ Dec (F := F) A :=
    fun A σ => SetLike.ext_iff.1 (hfam A).1 σ
  have key : (Kum.XDual 1 U (ZMod l) (ZMod l)).map (LinearEquiv.funCongrLeft (ZMod l) (ZMod l) e).toLinearMap =
      Kum.XDual 1 (U.comap (galEmb ℚ F Ω)) (ZMod l) (ZMod l) := by
    ext φ
    constructor
    · rintro ⟨ψ, ⟨h1, h2, h3, h4⟩, rfl⟩
      exact ⟨h1.comp_continuous hc, fun a b => h2 (e a) (e b), fun A u h => h3 A (e u) ((hI A _).2 h),
        fun A hA u h => h4 A hA (e u) ((hD A _).2 h)⟩
    · rintro ⟨h1, h2, h3, h4⟩
      exact ⟨φ ∘ e.symm, ⟨h1.comp_continuous hc', fun a b => h2 (e.symm a) (e.symm b),
        fun A u h => h3 A (e.symm u) ((hI A _).1 h), fun A hA u h => h4 A hA (e.symm u) ((hD A _).1 h)⟩, rfl⟩
  unfold GC.clRk
  rw [← key]
  exact ((LinearEquiv.funCongrLeft (ZMod l) (ZMod l) e).submoduleMap _).rank_eq.symm
end

section

open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Pr UpperTheory.V.Fr UpperTheory.V

theorem UpperTheory.V.Fr.sc_disc :
    ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (K : Type) [Field K] [NumberField K] [Algebra K Ω], Module.finrank ℚ K = 2 → (∀ B : ValuationSubring Ω, B.valuation (l : Ω) < 1 → Ine (F := ℚ) B ≤ galOf ℚ K Ω) → ¬ (l : ℤ) ∣ discr K := by
  intro Ω _ _ _ l _ K _ _ _ h2 hB
  haveI : Algebra.IsQuadraticExtension ℚ K := ⟨h2⟩
  haveI : IsGalois ℚ K := {}
  have hl : l.Prime := Fact.out
  rw [← (UpperTheory.V.CF.unramIff).2.1 K l hl, (UpperTheory.V.CF.unramIff).1 K l hl]
  intro w hw
  obtain ⟨A, hA⟩ := ReciprocityTheory.Gal.exists_isPlaceOver (F := K) Ω w
  have hv : A.valuation (l : Ω) < 1 := by
    have h := (hA (l : 𝓞 K)).2 hw
    simpa only [map_natCast] using h
  have hI := hB A hv
  rw [← UpperTheory.V.CF.ineAbs ℚ K Ω A w hA, Subgroup.eq_bot_iff_forall]
  rintro _ ⟨σ, hσ, rfl⟩
  have hσ' : ∀ x : K, σ (algebraMap K Ω x) = algebraMap K Ω x := hI hσ
  ext x
  apply (algebraMap K Ω).injective
  show algebraMap K Ω (σ.restrictNormal K x) = algebraMap K Ω x
  rw [AlgEquiv.restrictNormal_commutes]
  exact hσ' x
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Pr UpperTheory.V.Fr UpperTheory.V

private theorem exists_char_of_index {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    (l : ℕ) [Fact l.Prime] (H : Subgroup Γ) (ho : IsOpen (H : Set Γ)) (hc : commutator Γ ≤ H)
    (hi : H.index = l) :
    ∃ φ : Γ → ZMod l, IsLocallyConstant φ ∧ (∀ a b, φ (a * b) = φ a + φ b) ∧ ∀ a, φ a = 0 ↔ a ∈ H := by
  have hN : H.Normal := by
    refine ⟨fun a ha g => ?_⟩
    have hc' : g * a * g⁻¹ * a⁻¹ ∈ H :=
      hc (Subgroup.commutator_mem_commutator (Subgroup.mem_top g) (Subgroup.mem_top a))
    have h2 := H.mul_mem hc' ha
    simpa using h2
  have hQ : Nat.card (Γ ⧸ H) = l := hi
  have hM : Nat.card (Multiplicative (ZMod l)) = l := by
    rw [Nat.card_eq_fintype_card]
    simp
  haveI : IsCyclic (Γ ⧸ H) := isCyclic_of_prime_card hQ
  haveI : IsCyclic (Multiplicative (ZMod l)) := isCyclic_of_prime_card hM
  let e : (Γ ⧸ H) ≃* Multiplicative (ZMod l) := mulEquivOfCyclicCardEq (hQ.trans hM.symm)
  let f : Γ →* Multiplicative (ZMod l) := (e : (Γ ⧸ H) →* Multiplicative (ZMod l)).comp (QuotientGroup.mk' H)
  have hadd : ∀ a b, Multiplicative.toAdd (f (a * b)) = Multiplicative.toAdd (f a) + Multiplicative.toAdd (f b) := by
    intro a b
    rw [map_mul, toAdd_mul]
  have hker : ∀ a, Multiplicative.toAdd (f a) = 0 ↔ a ∈ H := by
    intro a
    have h1 : Multiplicative.toAdd (f a) = 0 ↔ f a = 1 := by
      constructor
      · intro h
        exact Multiplicative.toAdd.injective (by simpa using h)
      · intro h
        rw [h]
        rfl
    rw [h1]
    simp only [f, MonoidHom.coe_comp, Function.comp_apply, QuotientGroup.mk'_apply, MonoidHom.coe_coe,
      MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff]
  refine ⟨fun a => Multiplicative.toAdd (f a), ?_, hadd, hker⟩
  rw [IsLocallyConstant.iff_exists_open]
  intro x
  refine ⟨(fun h => x * h) '' (H : Set Γ), isOpenMap_mul_left x _ ho, ⟨1, H.one_mem, mul_one x⟩, ?_⟩
  rintro _ ⟨h, hh, rfl⟩
  show Multiplicative.toAdd (f (x * h)) = Multiplicative.toAdd (f x)
  rw [hadd, (hker h).2 hh, add_zero]

theorem UpperTheory.V.Fr.st_tame :
    ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (k : Type) [Field k] [CharP k l] (A : ValuationSubring Ω), ¬ A.valuation (l : Ω) < 1 → ∀ H : Subgroup (G ℚ Ω), IsOpen (H : Set (G ℚ Ω)) → commutator (G ℚ Ω) ≤ H → H.index = l → ¬ Ine (F := ℚ) A ≤ H → ∀ y : G ℚ Ω → k, IsLocallyConstant y → (∀ s ∈ Ine (F := ℚ) A, ∀ t ∈ Ine (F := ℚ) A, y (s * t) = y s + y t) → ∀ s ∈ Ine (F := ℚ) A ⊓ H, y s = 0 := by
  intro Ω _ _ _ l _ k _ _ A hA H ho hc hi hIH y hy hyadd s hs
  obtain ⟨φ, hφc, hφa, hφk⟩ := exists_char_of_index l H ho hc hi
  obtain ⟨γ, hγ⟩ := UpperTheory.V.Two.tameGen ℚ Ω l A hA
  let φI : ↥(Ine (F := ℚ) A) → ZMod l := fun σ => φ σ
  have hφIc : IsLocallyConstant φI := hφc.comp_continuous continuous_subtype_val
  have hφIa : ∀ a b : ↥(Ine (F := ℚ) A), φI (a * b) = φI a + φI b := fun a b => hφa _ _
  have hγne : φI γ ≠ 0 := by
    intro h0
    apply hIH
    intro σ hσ
    exact (hφk σ).1 (hγ φI hφIc hφIa h0 ⟨σ, hσ⟩)
  letI : Algebra (ZMod l) k := ZMod.algebra k l
  rw [← Module.forall_dual_apply_eq_zero_iff (ZMod l)]
  intro μ
  let c : ZMod l := μ (y γ) / φI γ
  let ψ : ↥(Ine (F := ℚ) A) → ZMod l := fun σ => μ (y σ) - c * φI σ
  have hyI : IsLocallyConstant (fun σ : ↥(Ine (F := ℚ) A) => y σ) := hy.comp_continuous continuous_subtype_val
  have hψc : IsLocallyConstant ψ := IsLocallyConstant.comp₂ hyI hφIc (fun u v => μ u - c * v)
  have hψa : ∀ a b : ↥(Ine (F := ℚ) A), ψ (a * b) = ψ a + ψ b := by
    intro a b
    simp only [ψ]
    rw [hφIa, Subgroup.coe_mul, hyadd _ a.2 _ b.2, map_add (f := _)]
    ring
  have hψγ : ψ γ = 0 := by
    simp only [ψ, c]
    rw [div_mul_cancel₀ _ hγne, sub_self]
  have h := hγ ψ hψc hψa hψγ ⟨s, hs.1⟩
  have h0 : φI ⟨s, hs.1⟩ = 0 := (hφk s).2 hs.2
  simp only [ψ] at h
  rw [h0, mul_zero, sub_zero] at h
  exact h
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Pr UpperTheory.V.Fr UpperTheory.V

private theorem sd_locConst {Γ A : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [Group A] (ψ : Γ →* A)
    (h : IsOpen (ψ.ker : Set Γ)) : IsLocallyConstant ψ :=
  _root_.UpperTheory.Reformulated.B.LocallyConstantOfKernel.lc_of_ker ψ h

theorem UpperTheory.V.Fr.st_desc :
    ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (S : Set (HeightOneSpectrum (𝓞 ℚ))) (C : Type) [Group C] (κ : G ℚ Ω →* C), IsOpen (κ.ker : Set (G ℚ Ω)) → (∀ v ∉ S, ∀ A : ValuationSubring Ω, IsPlaceOver A v → Ine (F := ℚ) A ≤ κ.ker) → ∃ κS : GS Ω S →* C, κS.comp (toGS Ω S) = κ ∧ IsLocallyConstant κS := by
  intro Ω _ _ _ S C _ κ ho hI
  have hN : NS Ω S ≤ κ.ker := by
    refine Subgroup.topologicalClosure_minimal _ (Subgroup.normalClosure_le_normal ?_)
      (Subgroup.isClosed_of_isOpen _ ho)
    intro s hs
    simp only [Set.mem_iUnion] at hs
    obtain ⟨v, hv, A, hA, hs⟩ := hs
    exact hI v hv A hA hs
  refine ⟨QuotientGroup.lift (NS Ω S) κ hN, MonoidHom.ext fun _ => rfl, fun T => ?_⟩
  rw [← (QuotientGroup.isQuotientMap_mk (NS Ω S)).isOpen_preimage]
  exact sd_locConst κ ho T
end

section

open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Pr UpperTheory.V.Fr UpperTheory.V

theorem UpperTheory.V.Fr.sc_cong :
    ∀ (l : ℕ) [Fact l.Prime] (c : Coef l) (u : c.Oˣ) (a : (Qbar l)ˣ), ‖a.val - u.val.1‖ < 1 → Sd.Cong (a ^ 2) 1 → Units.map (residue c.O).toMonoidHom u ^ 2 = 1 := by
  intro l _ c u a ha hcong
  have hu := (sc_norm l c u.val).1
  unfold Sd.Cong at hcong
  rw [Units.val_pow_eq_pow_val, Units.val_one] at hcong
  set x : PadicAlgCl l := ((u.val : c.O) : PadicAlgCl l) with hx
  set y : PadicAlgCl l := a.val with hy
  have hy1 : ‖y‖ ≤ 1 := by
    have h := IsUltrametricDist.norm_add_le_max (y - x) x
    rw [sub_add_cancel] at h
    exact h.trans (max_le ha.le hu)
  have hxy : ‖x + y‖ ≤ 1 := (IsUltrametricDist.norm_add_le_max x y).trans (max_le hu hy1)
  have hmem : (u.val ^ 2 - 1 : c.O) ∈ maximalIdeal c.O := by
    rw [(sc_norm l c _).2]
    have e : ((u.val ^ 2 - 1 : c.O) : PadicAlgCl l) = (x - y) * (x + y) + (y ^ 2 - 1) := by
      rw [hx]
      push_cast
      ring
    rw [e]
    refine lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt ?_ hcong)
    rw [norm_mul]
    have : ‖x - y‖ < 1 := by rw [← norm_neg, neg_sub]; exact ha
    nlinarith [norm_nonneg (x - y), norm_nonneg (x + y)]
  ext
  simp only [Units.val_pow_eq_pow_val, Units.coe_map, Units.val_one]
  rw [← sub_eq_zero]
  have h0 := (residue_eq_zero_iff _).2 hmem
  rw [map_sub, map_pow, map_one] at h0
  exact h0
end
