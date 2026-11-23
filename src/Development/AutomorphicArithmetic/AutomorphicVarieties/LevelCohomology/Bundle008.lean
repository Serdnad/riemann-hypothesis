module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.Bundle002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Bundle009
import Mathlib.Algebra.Module.StablyFree.Basic
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.AdjointDiagonalRepPreservesWeightPiece
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.Bundle001
public import Mathlib.NumberTheory.DirichletCharacter.Basic
public import Mathlib.NumberTheory.LegendreSymbol.ZModChar
public import ReciprocityTheory.Hypotheses.GalCohDefs
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.RestrictionMemInvariantH1
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.DirichletPrimeToLPartMulLPowerPart
import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.Bundle006
import Formalism.ConjugateSelfDual.Bundle001
import ReciprocityTheory.GaloisValuations.GlobalA

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module UpperTheory.V UpperTheory.V.X

private theorem ker_open {k Γ M : Type} [Field k] [Group Γ] [TopologicalSpace Γ] [AddCommGroup M] [Module k M]
    [Module.Finite k M] [TopologicalSpace M] [DiscreteTopology M] (ρ : Representation k Γ M) (h : ContAction ρ) :
    IsOpen (ρ.ker : Set Γ) := by
  let b := Module.finBasis k M
  have hset : (ρ.ker : Set Γ) = ⋂ i, {g | ρ g (b i) = b i} := by
    ext g
    simp only [SetLike.mem_coe, MonoidHom.mem_ker, Set.mem_iInter, Set.mem_setOf_eq]
    constructor
    · intro hg i
      rw [hg]
      rfl
    · intro hg
      exact b.ext fun i => by simpa using hg i
  rw [hset]
  apply isOpen_iInter_of_finite
  intro i
  have hc : Continuous fun g : Γ => ρ g (b i) :=
    (show Continuous fun p : Γ × M => ρ p.1 p.2 from h).comp (continuous_id.prodMk continuous_const)
  exact hc.isOpen_preimage {b i} (isOpen_discrete _)

private theorem finite_compactly_supported_H1 {k Γ M : Type} [Field k] [Group Γ] [TopologicalSpace Γ] [AddCommGroup M] [Module k M]
    [Module.Finite k M] [TopologicalSpace M] [DiscreteTopology M] (F : Alg.Frame Γ) (ρ : Representation k Γ M)
    [Module.Finite k (H1 ρ)] : Module.Finite k (F.H1c ρ) := by
  have hB : (B1 ρ).FG := by
    show (LinearMap.range (d0 ρ)).FG
    rw [LinearMap.range_eq_map]
    exact (Module.Finite.fg_top).map _
  haveI : IsNoetherian k ↥(B1 ρ) := isNoetherian_of_fg_of_noetherian _ hB
  have hK : (Submodule.comap (Z1 ρ).subtype (B1 ρ)).FG :=
    Submodule.fg_of_fg_map_injective (Z1 ρ).subtype Subtype.val_injective
      (Submodule.FG.of_le_of_isNoetherian (Submodule.map_comap_le _ _))
  have hZ : (⊤ : Submodule k ↥(Z1 ρ)).FG := by
    apply Submodule.fg_of_fg_map_of_fg_inf_ker (Submodule.mkQ (Submodule.comap (Z1 ρ).subtype (B1 ρ)))
    · exact IsNoetherian.noetherian _
    · rw [top_inf_eq, Submodule.ker_mkQ]
      exact hK
  haveI : Module.Finite k ↥(Z1 ρ) := ⟨hZ⟩
  have hZ1 : (Z1 ρ).FG := Module.Finite.iff_fg.mp inferInstance
  have hP : ((Z1 ρ).prod (⊤ : Submodule k (F.T → M))).FG := hZ1.prod Module.Finite.fg_top
  haveI := isNoetherian_of_fg_of_noetherian _ hP
  have hle : F.H1c ρ ≤ (Z1 ρ).prod ⊤ := by
    rintro x ⟨hlc, hcoc, -, -, -⟩
    exact ⟨⟨hlc.continuous, hcoc⟩, trivial⟩
  exact Module.Finite.iff_fg.mpr (Submodule.FG.of_le_of_isNoetherian hle)

theorem UpperTheory.V.X.framed_h1_euler_formula :
    ∀ {k Γ M : Type} [Field k] [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [AddCommGroup M] [Module k M] [Module.Finite k M] [TopologicalSpace M] [DiscreteTopology M] (F : Alg.Frame Γ) (ρ : Representation k Γ M), ContAction ρ → (∀ q, ∀ n ∈ F.N q, ρ (F.ψ q n) = 1) → Module.Finite k (H1 ρ) → Module.Finite k (F.H1c ρ) ∧ finrank k (F.H1c ρ) + finrank k (H0 ρ) = finrank k (selF F ρ) + ∑ v, finrank k (H0 (ρ.comp (F.φ v))) := by
  intro k Γ M _ _ _ _ _ _ _ _ _ F ρ hc hN hH
  refine ⟨finite_compactly_supported_H1 F ρ, ?_⟩
  have e := Alg.finrank_compact_support_H1 k Γ M ρ (ker_open ρ hc) F hN hH
  have hs : finrank k ↥(selF F ρ) = finrank k ↥(Sha1 ρ F.φ F.hφ ⊓
      Sel ρ F.ψ F.hψ fun q => H1ur (ρ.comp (F.ψ q)) (F.N q)) := rfl
  rw [hs]
  omega
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.X

section SlopeTestRemainingChoices
open UpperTheory.V.U3 UpperTheory.V.UnitaryThreeInertia

private def eGb {k : Type} [CommRing k] (a : k) : Gb (k := k) (-2) :=
  (⟨Matrix.single 2 0 a, by
    intro i j h
    fin_cases i <;> fin_cases j <;> first | (exfalso; revert h; decide) | simp⟩ : gw (R := k) (-2))

private theorem eGb_val {k : Type} [CommRing k] (a : k) : (eGb a).val 2 0 = a := by
  show Matrix.single 2 0 a 2 0 = a
  exact Matrix.single_apply_same _ _ _

private theorem gb_ext {k : Type} [CommRing k] {X Y : Gb (k := k) (-2)} (h : X.val 2 0 = Y.val 2 0) : X = Y := by
  have hX : ∀ a b, UpperTheory.V.U3.wt a b ≠ -2 → (X.val : Matrix (Fin 3) (Fin 3) k) a b = 0 := X.2
  have hY : ∀ a b, UpperTheory.V.U3.wt a b ≠ -2 → (Y.val : Matrix (Fin 3) (Fin 3) k) a b = 0 := Y.2
  apply Subtype.ext
  ext a b
  by_cases hab : a = 2 ∧ b = 0
  · obtain ⟨rfl, rfl⟩ := hab
    exact h
  · have hw : UpperTheory.V.U3.wt a b ≠ -2 := by
      revert hab
      fin_cases a <;> fin_cases b <;> decide
    exact (hX a b hw).trans (hY a b hw).symm

private theorem gb_add {k : Type} [CommRing k] (X Y : Gb (k := k) (-2)) : (X + Y).val 2 0 = X.val 2 0 + Y.val 2 0 := rfl
private theorem gb_sub {k : Type} [CommRing k] (X Y : Gb (k := k) (-2)) : (X - Y).val 2 0 = X.val 2 0 - Y.val 2 0 := rfl

private theorem gb_rep {k D : Type} [CommRing k] [Group D] (η : D →* ℤˣ) (Ψ : D →* kˣ) (g : D) (X : Gb (k := k) (-2))
    (c : k) (hc : c * (Ψ g : k) ^ 2 = ((η g : ℤ) : k)) :
    (UnitaryThreeInertia.gRep η Ψ (-2) g X).val 2 0 = c * X.val 2 0 := by
  rw [gRep_val, adRep_baseLift_apply]
  have hw : UpperTheory.V.U3.wt 2 0 = -2 := by decide
  have r0 : Fin.rev (0 : Fin 3) = 2 := rfl
  have r2 : Fin.rev (2 : Fin 3) = 0 := rfl
  rw [hw, r0, r2, zpow_neg, zpow_ofNat]
  have hc' : c = ((η g : ℤ) : k) * (((Ψ g ^ 2)⁻¹ : kˣ) : k) := by
    have h0 : c * (((Ψ g ^ 2 : kˣ)) : k) * (((Ψ g ^ 2)⁻¹ : kˣ) : k) = c :=
      Units.mul_inv_cancel_right _ _
    rw [Units.val_pow_eq_pow_val, hc] at h0
    exact h0.symm
  rw [hc']
  rcases Int.units_eq_one_or (η g) with h1 | h1
  · rw [ite_eq_left h1, h1]
    simp only [Units.val_one, Int.cast_one]
    ring
  · rw [ite_eq_right (by rw [h1]; decide), h1]
    simp only [Units.val_neg, Units.val_one, Int.cast_neg, Int.cast_one]
    ring

end SlopeTestRemainingChoices

theorem UpperTheory.V.X.xppOf :
    ∀ {O : Type} [CommRing O] [IsLocalRing O] {G' Γ ι : Type} [Group G'] [TopologicalSpace G'] [IsTopologicalGroup G'] [Group Γ] [TopologicalSpace Γ] (F : UnitaryThreeInertia.Frame O G' Γ ι) (γ : Γ → ResidueField O), (∀ g, γ g * (F.Ψbar g : ResidueField O) ^ 2 = ((F.η g : ℤ) : ResidueField O)) → (∀ z : Γ → ResidueField O, IsLocallyConstant z → (∀ g h, z (g * h) = z g + γ g * z h) → (∀ v, v ≠ F.vl → ∀ s ∈ F.Nv v, z (F.loc v s) = 0) → (∃ m, ∀ s, z (F.loc F.vl s) = γ (F.loc F.vl s) * m - m) → ∃ m, ∀ g, z g = γ g * m - m) → F.Xpp := by
  intro O iR iL G' Γ ι iG iT iTG iΓ iTΓ F γ hγ hmain
  show Subsingleton (F.selmerCohomologyQuotient (-2))
  refine Submodule.Quotient.subsingleton_iff.2 ?_
  rw [eq_top_iff]
  rintro ⟨f, hf⟩ -
  show f ∈ B1 (F.gbar (-2))
  obtain ⟨hZ, hL⟩ := Submodule.mem_inf.1 hf
  obtain ⟨hcont, hcoc⟩ := (mem_Z1_iff_cocycle _ _).1 hZ
  have hZL : ∀ v, F.res1 (-2) v f ∈ Z1 (F.gloc (-2) v) ∧
      (v ≠ F.vl → ∀ s ∈ F.Nv v, F.res1 (-2) v f s = 0) ∧
      (v = F.vl → (-2 : ℤ) < 0 → F.res1 (-2) v f ∈ B1 (F.gloc (-2) v)) ∧
      (v = F.vl → (-2 : ℤ) = 0 → ∀ s ∈ F.Iv v, F.res1 (-2) v f s = 0) :=
    fun v => (Submodule.mem_iInf _).1 hL v
  have hlc : IsLocallyConstant (fun g => (f g).val 2 0) :=
    ((IsLocallyConstant.iff_continuous _).2 hcont).comp
      (fun X : UpperTheory.V.UnitaryThreeInertia.Gb (k := ResidueField O) (-2) => X.val 2 0)
  obtain ⟨m, hm⟩ := hmain (fun g => (f g).val 2 0) hlc
    (by
      intro g h
      show (f (g * h)).val 2 0 = (f g).val 2 0 + γ g * (f h).val 2 0
      rw [hcoc g h, gb_add, gb_rep F.η F.Ψbar g _ (γ g) (hγ g)])
    (by
      intro v hv s hs
      have h0 : f (F.loc v s) = 0 := (hZL v).2.1 hv s hs
      show (f (F.loc v s)).val 2 0 = 0
      rw [h0]
      rfl)
    (by
      obtain ⟨m, hm⟩ := (mem_coboundaries1 _ _).1 ((hZL F.vl).2.2.1 rfl (by norm_num))
      refine ⟨m.val 2 0, fun s => ?_⟩
      have h' : f (F.loc F.vl s) = F.gbar (-2) (F.loc F.vl s) m - m := hm s
      show (f (F.loc F.vl s)).val 2 0 = _
      rw [h', gb_sub, gb_rep F.η F.Ψbar _ _ (γ _) (hγ _)])
  rw [mem_coboundaries1]
  refine ⟨eGb m, fun g => gb_ext ?_⟩
  rw [gb_sub, gb_rep F.η F.Ψbar g _ (γ g) (hγ g), eGb_val]
  exact hm g
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.X

theorem UpperTheory.V.X.primProd :
    ∀ (O : Type) [CommRing O] [IsDomain O] (M N : ℕ) [NeZero M] [NeZero N] (χ : DirichletCharacter O M) (θ : DirichletCharacter O N), ∃ (f : ℕ) (φ : DirichletCharacter O f), φ.IsPrimitive ∧ f ∣ M * θ.conductor ∧ (∀ t : ℕ, χ ^ t = 1 → θ ^ t = 1 → φ ^ t = 1) ∧ ∀ a : ℤ, IsCoprime a (M * N : ℕ) → φ a = χ a * θ a := by
  intro O _ _ M N _ _ χ θ
  have hc0 : θ.conductor ≠ 0 := θ.conductor_ne_zero
  haveI : NeZero θ.conductor := ⟨hc0⟩
  haveI : NeZero (M * θ.conductor) := ⟨mul_ne_zero (NeZero.ne M) hc0⟩
  set θ' := θ.primitiveCharacter with hθe
  have hM : M ∣ M * θ.conductor := dvd_mul_right M _
  have hC : θ.conductor ∣ M * θ.conductor := dvd_mul_left _ M
  set ψ : DirichletCharacter O (M * θ.conductor) :=
    DirichletCharacter.changeLevel hM χ * DirichletCharacter.changeLevel hC θ' with hψe
  refine ⟨ψ.conductor, ψ.primitiveCharacter, ψ.primitiveCharacter_isPrimitive, ψ.conductor_dvd_level, ?_, ?_⟩
  · intro t hχ hθ
    have hθ1 : θ' ^ t = 1 := by
      rw [← DirichletCharacter.changeLevel_eq_one_iff θ.conductor_dvd_level, map_pow,
        DirichletCharacter.changeLevel_primitiveCharacter]
      exact hθ
    have hψ1 : ψ ^ t = 1 := by
      rw [hψe, mul_pow, ← map_pow, ← map_pow, hχ, hθ1, map_one, map_one, mul_one]
    rw [← DirichletCharacter.changeLevel_eq_one_iff ψ.conductor_dvd_level, map_pow,
      DirichletCharacter.changeLevel_primitiveCharacter]
    exact hψ1
  · intro a ha
    rw [Nat.cast_mul] at ha
    have haM : IsCoprime a (M : ℤ) := ha.of_mul_right_left
    have haN : IsCoprime a (N : ℤ) := ha.of_mul_right_right
    have haC : IsCoprime a (θ.conductor : ℤ) :=
      haN.of_isCoprime_of_dvd_right (Int.natCast_dvd_natCast.mpr θ.conductor_dvd_level)
    have haMC : IsCoprime a ((M * θ.conductor : ℕ) : ℤ) := by
      rw [Nat.cast_mul]
      exact haM.mul_right haC
    rw [ψ.primitiveCharacter_apply_of_isCoprime haMC, hψe, MulChar.mul_apply,
      DirichletCharacter.changeLevel_eq_cast_of_dvd' χ hM haMC,
      DirichletCharacter.changeLevel_eq_cast_of_dvd' θ' hC haMC,
      θ.primitiveCharacter_apply_of_isCoprime haN]
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.X

private theorem UpperTheory.V.X.xiSq_ft {R : Type} [CommRing R] {n d : ℕ} [NeZero n] (χ : DirichletCharacter R n)
    (hd : d ∣ n) : χ.FactorsThrough d ↔ ∀ a : ℤ, IsCoprime a n → (d : ℤ) ∣ a - 1 → χ a = 1 := by
  constructor
  · rintro ⟨hd', χ₀, rfl⟩ a ha hda
    rw [DirichletCharacter.changeLevel_eq_cast_of_dvd' χ₀ hd' ha]
    have : ((a : ℤ) : ZMod d) = 1 := by
      have h0 := (ZMod.intCast_zmod_eq_zero_iff_dvd (a - 1) d).mpr hda
      push_cast at h0
      exact sub_eq_zero.mp h0
    rw [this, map_one]
  · intro h
    rw [DirichletCharacter.factorsThrough_iff_ker_unitsMap hd]
    intro x hx
    rw [MonoidHom.mem_ker] at hx ⊢
    set a : ℤ := ((x : ZMod n).val : ℤ) with ha_def
    have hax : ((a : ℤ) : ZMod n) = (x : ZMod n) := by
      simp [ha_def, ZMod.natCast_zmod_val]
    have hcop : IsCoprime a n := by
      have hu : IsUnit ((a : ℤ) : ZMod n) := by rw [hax]; exact x.isUnit
      rw [ZMod.coe_int_isUnit_iff_isCoprime] at hu
      exact hu.symm
    have hd1 : (d : ℤ) ∣ a - 1 := by
      apply (ZMod.intCast_zmod_eq_zero_iff_dvd (a - 1) d).mp
      have h1 := congrArg (fun u : (ZMod d)ˣ => (u : ZMod d)) hx
      simp only [ZMod.unitsMap_val, Units.val_one] at h1
      rw [ZMod.cast_eq_val] at h1
      push_cast
      rw [ha_def]
      push_cast
      rw [h1, sub_self]
    have := h a hcop hd1
    rw [hax] at this
    ext
    simpa using this

private theorem UpperTheory.V.X.xiSq_cong {R : Type} [CommRing R] {n : ℕ} (χ : DirichletCharacter R n)
    {a b : ℤ} (h : (n : ℤ) ∣ a - b) : χ a = χ b := by
  congr 1
  exact (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mpr (dvd_sub_comm.mp h)

private theorem UpperTheory.V.X.xiSq_cop (t : ℤ) (m : ℕ) : IsCoprime (1 + 2 * t) ((2 ^ m : ℕ) : ℤ) := by
  push_cast
  exact IsCoprime.pow_right ⟨1, -t, by ring⟩

private theorem UpperTheory.V.X.exists_primitive_square_twist {O : Type} [CommRing O] (k : ℕ) (ψ : DirichletCharacter O (2 ^ (k + 4)))
    (hψ : ψ.IsPrimitive) : ∃ ξ : DirichletCharacter O (2 ^ (k + 3)), ξ.IsPrimitive ∧
      ∀ a : ℤ, IsCoprime a ((2 ^ (k + 4) : ℕ) : ℤ) → ξ a = ψ a ^ 2 * ((ZMod.χ₄ a : ℤ) : O) := by
  have h4 : 4 ∣ 2 ^ (k + 4) := Dvd.intro (2 ^ k * 4) (by ring)
  let χ4O : DirichletCharacter O 4 := ZMod.χ₄.ringHomComp (Int.castRingHom O)
  let φ : DirichletCharacter O (2 ^ (k + 4)) := ψ ^ 2 * DirichletCharacter.changeLevel h4 χ4O
  have hsq : ∀ a : ℤ, ψ a ^ 2 = ψ ((a ^ 2 : ℤ) : ZMod (2 ^ (k + 4))) := by
    intro a
    rw [Int.cast_pow, map_pow]
  have h1 : ψ ((1 : ℤ) : ZMod (2 ^ (k + 4))) = 1 := by rw [Int.cast_one, map_one]
  have hc4 : ∀ a : ℤ, (4 : ℤ) ∣ a - 1 → ((ZMod.χ₄ a : ℤ) : O) = 1 := by
    intro a ha
    have := UpperTheory.V.X.xiSq_cong ZMod.χ₄ (n := 4) (a := a) (b := 1) (by exact_mod_cast ha)
    rw [this]
    simp
  have hval : ∀ a : ℤ, IsCoprime a ((2 ^ (k + 4) : ℕ) : ℤ) →
      φ a = ψ a ^ 2 * ((ZMod.χ₄ a : ℤ) : O) := by
    intro a ha
    simp only [φ, MulChar.coeToFun_mul, Pi.mul_apply, MulChar.pow_apply' _ two_ne_zero]
    rw [DirichletCharacter.changeLevel_eq_cast_of_dvd' _ h4 ha]
    simp [χ4O, MulChar.ringHomComp_apply]
  have hd : 2 ^ (k + 3) ∣ 2 ^ (k + 4) := pow_dvd_pow 2 (by omega)
  have hft : φ.FactorsThrough (2 ^ (k + 3)) := by
    rw [UpperTheory.V.X.xiSq_ft φ hd]
    intro a ha hda
    rw [hval a ha]
    obtain ⟨t, ht⟩ := hda
    push_cast at ht
    have ha' : a = 1 + 2 ^ (k + 3) * t := by linarith
    rw [hc4 a ⟨2 ^ (k + 1) * t, by rw [ha']; ring⟩, mul_one, hsq]
    rw [UpperTheory.V.X.xiSq_cong ψ (a := a ^ 2) (b := 1) ⟨t + 2 ^ (k + 2) * t ^ 2, by push_cast; rw [ha']; ring⟩]
    exact h1
  obtain ⟨hd', ξ, hξ⟩ := hft
  have hξv : ∀ a : ℤ, IsCoprime a ((2 ^ (k + 4) : ℕ) : ℤ) → ξ a = ψ a ^ 2 * ((ZMod.χ₄ a : ℤ) : O) := by
    intro a ha
    rw [← DirichletCharacter.changeLevel_eq_cast_of_dvd' ξ hd' ha, ← hξ, hval a ha]
  refine ⟨ξ, ?_, hξv⟩
  obtain ⟨j, hj, hj'⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp ξ.conductor_dvd_level
  show ξ.conductor = 2 ^ (k + 3)
  rw [hj']
  rcases Nat.lt_or_ge j (k + 3) with hlt | hge
  · exfalso
    have hf : ξ.FactorsThrough (2 ^ (k + 2)) :=
      DirichletCharacter.FactorsThrough.mono ξ ξ.factorsThrough_conductor
        (by rw [hj']; exact pow_dvd_pow 2 (by omega)) (pow_dvd_pow 2 (by omega))
    rw [UpperTheory.V.X.xiSq_ft ξ (pow_dvd_pow 2 (by omega))] at hf
    set b : ℤ := 1 + 2 * 2 ^ (k + 1) with hb
    have hb3 := hf b (by simpa [hb] using UpperTheory.V.X.xiSq_cop (2 ^ (k + 1)) (k + 3))
      ⟨1, by push_cast; rw [hb]; ring⟩
    rw [hξv b (by simpa [hb] using UpperTheory.V.X.xiSq_cop (2 ^ (k + 1)) (k + 4)),
      hc4 b ⟨2 ^ k, by rw [hb]; ring⟩, mul_one, hsq,
      UpperTheory.V.X.xiSq_cong ψ (a := b ^ 2) (b := 1 + 2 ^ (k + 3)) ⟨2 ^ k, by push_cast; rw [hb]; ring⟩] at hb3
    have hψf : ψ.FactorsThrough (2 ^ (k + 3)) := by
      rw [UpperTheory.V.X.xiSq_ft ψ hd]
      intro a ha hda
      obtain ⟨t, ht⟩ := hda
      push_cast at ht
      obtain ⟨s, hs | hs⟩ := Int.even_or_odd' t
      · rw [UpperTheory.V.X.xiSq_cong ψ (a := a) (b := 1) ⟨s, by push_cast; rw [hs] at ht; linear_combination ht⟩]
        exact h1
      · rw [UpperTheory.V.X.xiSq_cong ψ (a := a) (b := 1 + 2 ^ (k + 3)) ⟨s, by push_cast; rw [hs] at ht; linear_combination ht⟩]
        exact hb3
    have hle : ψ.conductor ≤ 2 ^ (k + 3) := Nat.sInf_le hψf
    have hpr : ψ.conductor = 2 ^ (k + 4) := hψ
    rw [hpr] at hle
    have := Nat.pow_lt_pow_right (a := 2) (by norm_num) (show k + 3 < k + 4 by omega)
    omega
  · congr 1
    omega

theorem UpperTheory.V.X.xiSq :
    ∀ (O : Type) [CommRing O] [IsDomain O], (2 : O) ≠ 0 → ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter O N) (c : ℕ), 4 ≤ c → χ.conductor = 2 ^ c → ∃ ξ : DirichletCharacter O (2 ^ (c - 1)), ξ.IsPrimitive ∧ ∀ a : ℤ, IsCoprime a N → ξ a = χ a ^ 2 * ((ZMod.χ₄ a : ℤ) : O) := by
  intro O _ _ _ N _ χ c hc hcond
  obtain ⟨k, rfl⟩ : ∃ k, c = k + 4 := ⟨c - 4, by omega⟩
  have hf : χ.FactorsThrough (2 ^ (k + 4)) := hcond ▸ χ.factorsThrough_conductor
  obtain ⟨hdv, ψ, hψχ⟩ := hf
  have hψp : ψ.IsPrimitive := by
    show ψ.conductor = 2 ^ (k + 4)
    have h := DirichletCharacter.conductor_changeLevel ψ hdv
    rw [← hψχ, hcond] at h
    exact h.symm
  obtain ⟨ξ, hp, hv⟩ := UpperTheory.V.X.exists_primitive_square_twist k ψ hψp
  refine ⟨ξ, hp, fun a ha => ?_⟩
  have ha' : IsCoprime a ((2 ^ (k + 4) : ℕ) : ℤ) :=
    ha.of_isCoprime_of_dvd_right (Int.natCast_dvd_natCast.mpr hdv)
  rw [hv a ha', hψχ, DirichletCharacter.changeLevel_eq_cast_of_dvd' ψ hdv ha]
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module UpperTheory.V UpperTheory.V.X

private theorem urIndex_mem {k D M : Type} [Field k] [Group D] [TopologicalSpace D] [AddCommGroup M] [Module k M]
    [TopologicalSpace M] [DiscreteTopology M] (ρ : Representation k D M) (J : Subgroup D) (f : Z1 ρ) :
    (Submodule.Quotient.mk f : H1 ρ) ∈ H1ur ρ J ↔ ∃ m, ∀ j ∈ J, f.1 j = ρ j m - m := by
  have hJc : Continuous J.subtype := continuous_subtype_val
  show resH1 ρ J.subtype hJc (Submodule.Quotient.mk f) = 0 ↔ _
  unfold resH1
  rw [Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero]
  show ((restrictCocycles1 ρ J.subtype hJc f : Z1 (ρ.comp J.subtype)) : J → M) ∈ B1 (ρ.comp J.subtype) ↔ _
  rw [mem_coboundaries1]
  constructor
  · rintro ⟨m, hm⟩
    refine ⟨m, fun j hj => ?_⟩
    have h := hm ⟨j, hj⟩
    rw [restrictCocycles1_apply ρ J.subtype hJc] at h
    simpa using h
  · rintro ⟨m, hm⟩
    refine ⟨m, fun j => ?_⟩
    rw [restrictCocycles1_apply ρ J.subtype hJc]
    simpa using hm j j.2

private theorem urIndex_avg {k Γ M : Type} [Field k] [Group Γ] [AddCommGroup M] [Module k M]
    (ρ : Representation k Γ M) (N : Subgroup Γ) (hN : (N.index : k) ≠ 0) (c : Γ → M)
    (hc : ∀ g h, c (g * h) = c g + ρ g (c h)) (h0 : ∀ n ∈ N, c n = 0) :
    ∃ m, ∀ g, c g = ρ g m - m := by
  classical
  have hNi : N.index ≠ 0 := fun h => hN (by rw [h, Nat.cast_zero])
  haveI : N.FiniteIndex := ⟨hNi⟩
  haveI : Fintype (Γ ⧸ N) := Fintype.ofFinite _
  have hconst : ∀ g n, n ∈ N → c (g * n) = c g := fun g n hn => by
    rw [hc, h0 n hn, map_zero, add_zero]
  let c' : Γ ⧸ N → M := Quotient.lift (s := QuotientGroup.leftRel N) c (fun a b hab => by
    have hab' : a⁻¹ * b ∈ N := QuotientGroup.leftRel_apply.1 hab
    have h := hconst a (a⁻¹ * b) hab'
    rw [mul_inv_cancel_left] at h
    exact h.symm)
  have hc' : ∀ (h : Γ) (x : Γ ⧸ N), c' (h • x) = c h + ρ h (c' x) := by
    intro h x
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
    show c (h * g) = c h + ρ h (c g)
    exact hc h g
  let S := ∑ x : Γ ⧸ N, c' x
  have hS : ∀ h, S = Fintype.card (Γ ⧸ N) • c h + ρ h S := by
    intro h
    calc S = ∑ x, c' (h • x) := (Equiv.sum_comp (MulAction.toPerm h) c').symm
      _ = ∑ x, (c h + ρ h (c' x)) := Finset.sum_congr rfl fun x _ => hc' h x
      _ = _ := by rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, map_sum]
  have hcard : (Fintype.card (Γ ⧸ N) : k) = N.index := by
    rw [Fintype.card_eq_nat_card]
    rfl
  refine ⟨-((N.index : k)⁻¹ • S), fun g => ?_⟩
  have h1 := hS g
  have h2 : S - ρ g S = (N.index : k) • c g := by
    rw [← hcard, Nat.cast_smul_eq_nsmul]
    nth_rewrite 1 [h1]
    rw [add_sub_cancel_right]
  rw [map_neg, map_smul, neg_sub_neg, ← smul_sub, h2, smul_smul, inv_mul_cancel₀ hN, one_smul]

theorem UpperTheory.V.X.urIndex :
    ∀ (l : ℕ) [Fact l.Prime] {k D M : Type} [Field k] [CharP k l] [Group D] [TopologicalSpace D] [AddCommGroup M] [Module k M] [TopologicalSpace M] [DiscreteTopology M] (ρ : Representation k D M), ContAction ρ → ∀ (I N : Subgroup D), N ≤ I → ¬ l ∣ N.relIndex I → H1ur ρ N = H1ur ρ I := by
  intro l _ k D M _ _ _ _ _ _ _ _ ρ hρ I N hNI hl
  ext c
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective (Submodule.comap (Z1 ρ).subtype (B1 ρ)) c
  refine (urIndex_mem ρ N f).trans (Iff.trans ?_ (urIndex_mem ρ I f).symm)
  constructor
  · rintro ⟨m, hm⟩
    have hf := ((mem_Z1_iff_cocycle ρ _).1 f.2).2
    let cI : I → M := fun j => f.1 j - (ρ j m - m)
    have hcI : ∀ g h : I, cI (g * h) = cI g + (ρ.comp I.subtype) g (cI h) := by
      intro g h
      simp only [cI, MonoidHom.comp_apply, Subgroup.coe_subtype, Subgroup.coe_mul, hf, map_mul,
        Module.End.mul_apply, map_sub]
      abel
    have h0 : ∀ n ∈ N.subgroupOf I, cI n = 0 := fun n hn => by
      simp only [cI]
      rw [hm n (Subgroup.mem_subgroupOf.1 hn), sub_self]
    have hidx : ((N.subgroupOf I).index : k) ≠ 0 := by
      have e : (N.subgroupOf I).index = N.relIndex I := rfl
      rw [e]
      intro h
      exact hl ((CharP.cast_eq_zero_iff k l _).1 h)
    obtain ⟨m', hm'⟩ := urIndex_avg (ρ.comp I.subtype) (N.subgroupOf I) hidx cI hcI h0
    refine ⟨m + m', fun j hj => ?_⟩
    have h := hm' ⟨j, hj⟩
    simp only [cI, MonoidHom.comp_apply, Subgroup.coe_subtype] at h
    rw [sub_eq_iff_eq_add] at h
    rw [h, map_add (f := _)]
    abel
  · rintro ⟨m, hm⟩
    exact ⟨m, fun j hj => hm j (hNI hj)⟩
end
