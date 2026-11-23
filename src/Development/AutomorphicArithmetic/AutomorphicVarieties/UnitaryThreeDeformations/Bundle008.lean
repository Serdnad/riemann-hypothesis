module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.IsCharZeroPt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.Bundle004
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.Bundle003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.NormEx
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.Bundle005
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle050
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open Matrix IsLocalRing ReciprocityTheory.Gal UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.UnitaryThreeInertia

private theorem map_tor {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (t : Aˣ) :
    GeneralLinearGroup.map f (tor A t) = tor B (Units.map f.toMonoidHom t) :=
  _root_.UpperTheory.Reformulated.B.H71.map_tor f t

private theorem map_conjBy {A B D : Type} [CommRing A] [CommRing B] [Group D] (f : A →+* B) (h : GL (Fin 3) A)
    (r : D →* GG (m := 3) (R := A)) :
    (GG.map f).comp (conjBy h r) = conjBy (GeneralLinearGroup.map f h) ((GG.map f).comp r) := by
  have e : GG.map f (GG.ofGL h) = GG.ofGL (GeneralLinearGroup.map f h) := by
    unfold GG.map
    rw [SemidirectProduct.map_inl]
  refine MonoidHom.ext fun g => ?_
  simp only [conjBy, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul, map_inv, e]

private theorem conj_conj {A D : Type} [CommRing A] [Group D] (h h' : GL (Fin 3) A)
    (r : D →* GG (m := 3) (R := A)) :
    conjBy (h * h') r = conjBy h (conjBy h' r) := by
  ext1 g
  simp only [conjBy, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul,
    _root_.mul_inv_rev, mul_assoc, MulAut.mul_apply]

private theorem conj_one {A D : Type} [CommRing A] [Group D]
    (r : D →* GG (m := 3) (R := A)) : conjBy 1 r = r := by
  ext1 g
  simp [conjBy]

private theorem conj_mat {A D : Type} [CommRing A] [Group D] (h : GL (Fin 3) A)
    (r : D →* GG (m := 3) (R := A)) (g : D) :
    (conjBy h r g).mat = (h : Matrix _ _ A) * (r g).mat *
      ((sgnAct 3 A (r g).right h⁻¹ : GL (Fin 3) A) : Matrix _ _ A) := by
  have : (conjBy h r g).left = h * (r g).left * sgnAct 3 A (r g).right h⁻¹ := by
    simp [conjBy, SemidirectProduct.mul_left, SemidirectProduct.inv_left]
  simp only [GG.mat, this, Units.val_mul]

private theorem setup {O : Type} [CommRing O] [IsLocalRing O] {G Γ ι : Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [Group Γ] [TopologicalSpace Γ] (F : Frame O G Γ ι) (hF : F.Ok) (g₁ : Γ)
    (hg : F.Marked g₁) {R : Type} [CommRing R] [Algebra O R] [IsLocalRing R]
    (r : Γ →* GG (m := 3) (R := R))
    (hr : Red F.η F.Ψ r) :
    ∃ Ψ : Γ →* (ResidueField R)ˣ, IsUnit (2 : R) ∧ Marks F.η Ψ F.c g₁ ∧
      (GG.map (residue R)).comp r = r0 F.η Ψ := by
  refine ⟨(Units.map ((residue R).comp (algebraMap O R)).toMonoidHom).comp F.Ψ, ?_,
    ⟨hF.csq, hF.ηc, by simp [hF.Ψc], hg.1, ?_⟩, ?_⟩
  · simpa [map_ofNat] using hF.two.map (algebraMap O R)
  · simpa using hg.2.map ((residue R).comp (algebraMap O R))
  · refine MonoidHom.ext fun g => SemidirectProduct.ext (Units.ext ?_) (hr.mult g)
    rw [unitaryThreeReflection_left, MonoidHom.comp_apply, MonoidHom.comp_apply, ← map_tor]
    ext a b
    exact Ideal.Quotient.eq.2 (hr.red g a b)

theorem UpperTheory.lift_along_surjection_graded :
    ∀ {O : Type} [CommRing O] [IsLocalRing O] {G Γ ι : Type} [Group G] [TopologicalSpace G]
      [IsTopologicalGroup G] [Group Γ] [TopologicalSpace Γ] (F : Frame O G Γ ι),
      F.Ok → ∀ g₁, F.Marked g₁ → ∀ {R R' : Type} [CommRing R] [Algebra O R] [IsCO O R]
        [CommRing R'] [Algebra O R'] [IsCO O R'] (q : R →ₐ[O] R'), Function.Surjective q →
      ∀ (r : Γ →* GG (m := 3) (R := R)) (r' : Γ →* GG (m := 3) (R := R')),
        F.Cond r → IsLocallyConstant (mats r) → _root_.UpperTheory.V.UnitaryThreeInertia.push q r = r' → F.CondN g₁ r' →
        ∃ r₂ : Γ →* GG (m := 3) (R := R), F.IsPt g₁ r₂ ∧ _root_.UpperTheory.V.UnitaryThreeInertia.push q r₂ = r' := by
  intro O _ _ G Γ ι _ _ _ _ _ F hF g₁ hg R R' _ _ _ _ _ _ q hq r r' hr hlc hp hr'
  haveI : IsAdicComplete (maximalIdeal R) R := IsCO.complete (O := O)
  have hm : ∀ x : R, q x ∈ maximalIdeal R' ↔ x ∈ maximalIdeal R := fun x => by
    rw [← res_eq_zero_iff O, res_map, res_eq_zero_iff]
  have hent : ∀ (h : GL (Fin 3) R), InHat (GeneralLinearGroup.map (q : R →+* R') h) ↔ InHat h := fun h => by
    refine forall_congr' fun a => forall_congr' fun b => ?_
    rw [← hm]
    refine iff_of_eq (congrArg (· ∈ maximalIdeal R') ?_)
    by_cases hab : a = b <;> simp [Matrix.one_apply, hab]
  obtain ⟨Ψ, h2, hM, hred⟩ := setup F hF g₁ hg r hr.toRed
  obtain ⟨Ψ', h2', hM', hred'⟩ := setup F hF g₁ hg r' hr'.toRed
  obtain ⟨h, hh, hN⟩ := exists_normalised F.η Ψ F.c g₁ r h2 hM hred
  have hpush : ∀ H : GL (Fin 3) R, _root_.UpperTheory.V.UnitaryThreeInertia.push q (conjBy H r) =
      conjBy (GeneralLinearGroup.map (q : R →+* R') H) r' := fun H => by
    rw [← hp]; exact map_conjBy _ _ _
  have hN' : Normalised F.c g₁ (conjBy (GeneralLinearGroup.map (q : R →+* R') h) r') := by
    rw [← hpush]
    refine ⟨?_, ?_, ?_⟩
    · rw [MonoidHom.comp_apply, GG.map_mat, hN.atc, Matrix.map_one _ (map_zero _) (map_one _)]
    · have := congrArg q hN.z12
      simpa [zmat] using this
    · have := congrArg q hN.z21
      simpa [zmat] using this
  obtain ⟨t', -, ht'⟩ := normalised_unique F.η Ψ' F.c g₁ r' _ h2' hM' hred' ((hent h).2 hh) hr'.norm hN'
  obtain ⟨t₀, ht₀⟩ := hq t'
  obtain ⟨t, rfl⟩ : IsUnit t₀ := by
    by_contra hn
    have := (hm t₀).2 hn
    rw [ht₀] at this
    exact this t'.isUnit
  have ht : Units.map (q : R →+* R').toMonoidHom t = t' := Units.ext ht₀
  have hH : GeneralLinearGroup.map (q : R →+* R') (tor R t⁻¹ * h) = 1 := by
    rw [map_mul, ht', map_tor, map_inv, ht, map_inv, inv_mul_cancel]
  have hHhat : InHat (tor R t⁻¹ * h) := by
    rw [← hent, hH]
    intro a b
    simp
  refine ⟨conjBy (tor R t⁻¹ * h) r, ⟨⟨(cond_conj F _ hHhat).2 r hr, ?_⟩, fun n => ?_⟩, ?_⟩
  · rw [conj_conj]
    exact (conjBy_tor _ _).2.2.1 _ _ hN
  · generalize tor R t⁻¹ * h = H
    have := (hlc.prodMk hF.η_cont).comp fun p : Matrix (Fin 3) (Fin 3) R × ℤˣ =>
      ((H : Matrix _ _ R) * p.1 * ((sgnAct 3 R p.2 H⁻¹ : GL (Fin 3) R) : Matrix _ _ R)).map
        (Ideal.Quotient.mk (maximalIdeal R ^ n))
    convert this using 1
    funext g
    rw [conj_mat, hr.mult g]
    rfl
  · rw [hpush, hH, conj_one]
end

section

open Matrix IsLocalRing ReciprocityTheory.Gal UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.UnitaryThreeInertia

private theorem UpperTheory.V.UnitaryThreeInertia.map_eq_zero_of_cc {O A σ : Type} [CommRing O] [CommRing A] [Fintype σ]
    (φ : MvPowerSeries σ O →+* A) (hφ : ∀ i, φ (MvPowerSeries.X i) = 0) (p : MvPowerSeries σ O)
    (hp : MvPowerSeries.constantCoeff p = 0) : φ p = 0 := by
  classical
  have hsupp : ∀ n : σ →₀ ℕ, n ≠ 0 → n.support.Nonempty :=
    fun n hn => Finsupp.support_nonempty_iff.mpr hn
  let sel : (σ →₀ ℕ) → σ → Prop := fun n i => ∃ h : n ≠ 0, (hsupp n h).choose = i
  let q : σ → MvPowerSeries σ O := fun i m =>
    if sel (m + Finsupp.single i 1) i then MvPowerSeries.coeff (m + Finsupp.single i 1) p else 0
  have hX : ∀ (n : σ →₀ ℕ) (i : σ) (f : MvPowerSeries σ O),
      MvPowerSeries.coeff n (MvPowerSeries.X i * f)
        = if Finsupp.single i 1 ≤ n then MvPowerSeries.coeff (n - Finsupp.single i 1) f else 0 := by
    intro n i f
    rw [show (MvPowerSeries.X i : MvPowerSeries σ O) = MvPowerSeries.monomial (Finsupp.single i 1) 1
      from rfl, MvPowerSeries.coeff_monomial_mul, one_mul]
  have hq : ∀ (i : σ) (m : σ →₀ ℕ), MvPowerSeries.coeff m (q i)
      = if sel (m + Finsupp.single i 1) i then MvPowerSeries.coeff (m + Finsupp.single i 1) p else 0 :=
    fun i m => rfl
  have hdec : p = ∑ i, MvPowerSeries.X i * q i := by
    ext n

    rw [map_sum]
    simp_rw [hX, hq]
    by_cases hn : n = 0
    · subst hn
      rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hp]
      symm
      apply Finset.sum_eq_zero
      intro i _
      rw [if_neg]
      intro hle
      have := hle i
      simp at this
    · set j := (hsupp n hn).choose with hj
      have hjmem : j ∈ n.support := (hsupp n hn).choose_spec
      have hjle : Finsupp.single j 1 ≤ n := by
        rw [Finsupp.single_le_iff]
        exact Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hjmem)
      rw [Finset.sum_eq_single j]
      · rw [if_pos hjle, tsub_add_cancel_of_le hjle, if_pos ⟨hn, rfl⟩]
      · intro b _ hb
        by_cases hble : Finsupp.single b 1 ≤ n
        · rw [if_pos hble, tsub_add_cancel_of_le hble, if_neg]
          rintro ⟨_, hb'⟩
          exact hb hb'.symm
        · rw [if_neg hble]
      · intro h
        exact absurd (Finset.mem_univ j) h

  rw [hdec, map_sum]
  apply Finset.sum_eq_zero
  intro i _
  rw [map_mul, hφ, zero_mul]

private theorem UpperTheory.V.UnitaryThreeInertia.map_eq_cc {O σ : Type} [CommRing O] [Fintype σ]
    (φ : MvPowerSeries σ O →ₐ[O] O) (hφ : ∀ i, φ (MvPowerSeries.X i) = 0) (p : MvPowerSeries σ O) :
    φ p = MvPowerSeries.constantCoeff p := by
  have h0 : MvPowerSeries.constantCoeff
      (p - algebraMap O (MvPowerSeries σ O) (MvPowerSeries.constantCoeff p)) = 0 := by
    rw [map_sub]
    exact sub_eq_zero.mpr rfl
  have h := UpperTheory.V.UnitaryThreeInertia.map_eq_zero_of_cc (φ : MvPowerSeries σ O →+* O) (fun i => hφ i) _ h0
  rw [map_sub, sub_eq_zero] at h
  have h2 : φ (algebraMap O (MvPowerSeries σ O) (MvPowerSeries.constantCoeff p))
      = MvPowerSeries.constantCoeff p := by
    rw [AlgHom.commutes]
    rfl
  exact h.trans h2

theorem UpperTheory.V.UnitaryThreeInertia.hasOrigin :
    ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] [CharZero O] [Finite (ResidueField O)]
      {G Γ ι : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
      [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] [T2Space Γ] [TotallyDisconnectedSpace Γ] [Finite ι] (F : Frame O G Γ ι), F.Ok →
    ∀ (g₁ : Γ), F.Marked g₁ → ∀ {R : Type} [CommRing R] [Algebra O R] [IsCO O R] (u : Γ →* GG (m := 3) (R := R)), F.IsUniv g₁ u →
    ∀ (W : WPres O ℤ R), F.Adapted u W → ∃ h : W.HasOrigin, _root_.UpperTheory.V.UnitaryThreeInertia.push (W.origin h) u = r0 F.η F.Ψ := by
  intro O _ _ _ _ _ _ G Γ ι _ _ _ _ _ _ _ _ _ _ _ _ _ F hF g₁ hg₁ R _ _ _ u hu W hW
  obtain ⟨f, hf, -⟩ := hu.univ O (F.rz O) (UpperTheory.V.UnitaryThreeInertia.isPt_rz F hF g₁)
  have hz : ∀ i, f (W.z i) = 0 := by
    intro i
    obtain ⟨g, a, b, -, -, hzi⟩ := hW.var i
    rw [hzi, map_sub]
    have h1 : f ((u g).mat a b) = ((F.rz O) g).mat a b := by
      rw [← hf]
      rfl
    have h2 : f (((F.rz R) g).mat a b) = ((F.rz O) g).mat a b := by
      show f (algebraMap O R _) = _
      rw [AlgHom.commutes]
      rfl
    rw [h1, h2, sub_self]
  haveI := W.fin
  let ψ : MvPowerSeries W.σ O →ₐ[O] O := f.comp W.π
  have hψ : ∀ p, ψ p = MvPowerSeries.constantCoeff p :=
    UpperTheory.V.UnitaryThreeInertia.map_eq_cc ψ (fun i => hz i)
  have hO : W.HasOrigin := by
    intro p hp
    rw [← hψ]
    show f (W.π p) = 0
    rw [hp, map_zero]
  refine ⟨hO, ?_⟩
  have heq : W.origin hO = f := by
    ext x
    obtain ⟨p, rfl⟩ := W.surj x
    rw [UpperTheory.V.Alg.WPres.origin_π, ← hψ]
    rfl
  rw [heq, hf]
  exact MonoidHom.ext fun g => rfl
end
