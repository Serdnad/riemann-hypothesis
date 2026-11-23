module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.DecompSigmaOrd
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Bundle006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PlacesOfRationals.Minkowski
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PlacesOfRationals.PlacesQ
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.NearSplit
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AdTransfer
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.PlacesQ
public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.Bundle007
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteMaximalSpectrumOfFiniteOfIsLocalRing
public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.LMemMax
public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.Bundle004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.SymplecticIwahori.Bundle002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.SymplecticIwahori.SmallFlag
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.SymplecticIwahori.TriSpec
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Topology.Algebra.ClopenNhdofOne
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RedIdeal

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

namespace UpperTheory.V.Ws.WeightCharacterKernel

private theorem open_ker {Ω K : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] [Field K] [TopologicalSpace K] [T2Space K]
    [ContinuousMul K] (δ : G ℚ Ω →* Kˣ) (hc : Continuous fun g => (δ g : K)) (N : ℕ) (hN : N ≠ 0)
    (h : ∀ A : ValuationSubring Ω, ∀ g ∈ Ine (F := ℚ) A, δ g ^ N = 1) : IsOpen (δ.ker : Set (G ℚ Ω)) := by
  classical
  have hpow : ∀ g, δ g ^ N = 1 := by
    intro g
    by_contra hg
    obtain ⟨a, ha⟩ : ∃ a : K, a = ((δ g ^ N : Kˣ) : K) := ⟨_, rfl⟩
    have ha1 : a ≠ 1 := fun h1 => hg (Units.val_eq_one.mp (ha ▸ h1))
    have hUo : IsOpen ((fun x => (δ x : K) ^ N) ⁻¹' ({a}ᶜ : Set K)) :=
      isOpen_compl_singleton.preimage (hc.pow N)
    have h1U : (1 : G ℚ Ω) ∈ ((fun x => (δ x : K) ^ N) ⁻¹' ({a}ᶜ : Set K)) := by
      simpa [eq_comm] using ha1
    obtain ⟨W, hW⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hUo h1U
    have hsup : W.toSubgroup ⊔ ((powMonoidHom N).comp δ).ker = ⊤ := by
      refine B3.minkowski Ω _ inferInstance (Subgroup.isOpen_mono le_sup_left W.isOpen) ?_
      intro B x hx
      apply Subgroup.mem_sup_right
      simpa using h B x hx
    have hg' : g ∈ W.toSubgroup ⊔ ((powMonoidHom N).comp δ).ker := hsup ▸ Subgroup.mem_top g
    obtain ⟨y, hy, z, hz, hyz⟩ := Subgroup.mem_sup_of_normal_left.mp hg'
    have hz' : δ z ^ N = 1 := by simpa using hz
    have heq : (δ y : K) ^ N = a := by
      rw [ha, ← hyz, map_mul, mul_pow, hz', mul_one, Units.val_pow_eq_pow_val]
    exact (hW hy) heq
  have hfin : ({x : K | x ^ N = 1} \ {1}).Finite := by
    refine (Finset.finite_toSet (Polynomial.nthRoots N (1 : K)).toFinset).subset ?_
    intro x hx
    simp only [Finset.mem_coe, Multiset.mem_toFinset]
    exact (Polynomial.mem_nthRoots (Nat.pos_of_ne_zero hN)).mpr hx.1
  have hopen : IsOpen ((fun g => (δ g : K)) ⁻¹' ({x : K | x ^ N = 1} \ {1})ᶜ) :=
    hfin.isClosed.isOpen_compl.preimage hc
  convert hopen using 1
  ext g
  simp only [SetLike.mem_coe, MonoidHom.mem_ker, Set.mem_preimage, Set.mem_compl_iff, Set.mem_diff,
    Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · intro h1
    simp [h1]
  · intro h2
    have hN1 : (δ g : K) ^ N = 1 := by rw [← Units.val_pow_eq_pow_val, hpow g, Units.val_one]
    exact Units.val_eq_one.mp (by by_contra hne; exact h2 ⟨hN1, hne⟩)

end UpperTheory.V.Ws.WeightCharacterKernel

open UpperTheory.V.Ws.WeightCharacterKernel in
theorem UpperTheory.V.Ws.wtChar :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good →
          ∀ (κ : G ℚ Ω →* PadicAlgCl l) (n : ℕ), Continuous κ → D.UnrT κ 1 → (∀ p ∈ D.Sb, ∀ g ∈ D.Ip p ⊓ D.ψ.ker, κ g = 1) →
          (∀ s ∈ D.Ip l ⊓ D.ψ.ker ⊓ D.om.ker, κ s = algebraMap ℤ_[l] (PadicAlgCl l) (cycZ ℚ Ω l s : ℤ_[l]) ^ n) →
          ∃ U : Subgroup (G ℚ Ω), IsOpen (U : Set (G ℚ Ω)) ∧ ∀ g ∈ U, κ g = algebraMap ℤ_[l] (PadicAlgCl l) (cycZ ℚ Ω l g : ℤ_[l]) ^ n := by
  intro Ω _ _ _ l _ c D hD κ n hκc hU hSb hl
  classical
  have hF := facts D hD
  have hrb : IsOpen (D.rbar.ker : Set (G ℚ Ω)) := hF.2.2.2.2.2.2.2.2.2.2.2.1
  have hom : IsOpen (D.om.ker : Set (G ℚ Ω)) := hF.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hps : IsOpen (D.ψ.ker : Set (G ℚ Ω)) := hD.psi_open
  obtain ⟨M, hM0, hM⟩ : ∃ M : ℕ, M ≠ 0 ∧ ∀ g : G ℚ Ω, g ^ M ∈ D.rbar.ker ⊓ D.ψ.ker ⊓ D.om.ker := by
    have ho : IsOpen ((D.rbar.ker ⊓ D.ψ.ker ⊓ D.om.ker : Subgroup (G ℚ Ω)) : Set (G ℚ Ω)) := by
      simpa only [Subgroup.coe_inf] using (hrb.inter hps).inter hom
    have := Subgroup.quotient_finite_of_isOpen _ ho
    exact ⟨_, Subgroup.index_ne_zero_of_finite, fun g => Subgroup.pow_index_mem _ g⟩
  have two : ∀ (B : ValuationSubring Ω) (p q : ℕ), p.Prime → q.Prime → p ≠ q →
      B.valuation (p : Ω) < 1 → ¬ B.valuation (q : Ω) < 1 := by
    intro B p q hp hq hpq h1 h2
    obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.mpr ((Nat.coprime_primes hp hq).mpr hpq)
    have hab' : (a : Ω) * p + (b : Ω) * q = 1 := by
      have := congrArg (Int.cast : ℤ → Ω) hab
      push_cast at this
      exact this
    have ha : B.valuation (a : Ω) ≤ 1 := (B.valuation_le_one_iff _).mpr (intCast_mem B a)
    have hb : B.valuation (b : Ω) ≤ 1 := (B.valuation_le_one_iff _).mpr (intCast_mem B b)
    have e1 : B.valuation ((a : Ω) * p) < 1 := by
      rw [map_mul]
      exact lt_of_le_of_lt (mul_le_of_le_one_left' ha) h1
    have e2 : B.valuation ((b : Ω) * q) < 1 := by
      rw [map_mul]
      exact lt_of_le_of_lt (mul_le_of_le_one_left' hb) h2
    have := B.valuation.map_add ((a : Ω) * p) ((b : Ω) * q)
    rw [hab', map_one] at this
    exact absurd this (not_le.mpr (max_lt e1 e2))
  have halg : Continuous fun x : ℤ_[l] => algebraMap ℤ_[l] (PadicAlgCl l) x := by
    have e : ∀ x : ℤ_[l], algebraMap ℤ_[l] (PadicAlgCl l) x = algebraMap ℚ_[l] (PadicAlgCl l) (x : ℚ_[l]) :=
      fun x => IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] _ x
    simp_rw [e]
    exact (continuous_algebraMap ℚ_[l] _).comp continuous_subtype_val
  let cU : G ℚ Ω →* (PadicAlgCl l)ˣ :=
    (Units.map (algebraMap ℤ_[l] (PadicAlgCl l)).toMonoidHom).comp (cycZ ℚ Ω l)
  have hcU : ∀ g, ((cU g : (PadicAlgCl l)ˣ) : PadicAlgCl l) = algebraMap ℤ_[l] (PadicAlgCl l) (cycZ ℚ Ω l g : ℤ_[l]) := by
    intro g
    rfl
  let δ : G ℚ Ω →* (PadicAlgCl l)ˣ := κ.toHomUnits * (cU ^ n)⁻¹
  have hδ : ∀ g, δ g = κ.toHomUnits g * (cU g ^ n)⁻¹ := fun g => by simp [δ]
  have hker : ∀ g, δ g = 1 ↔ κ g = algebraMap ℤ_[l] (PadicAlgCl l) (cycZ ℚ Ω l g : ℤ_[l]) ^ n := by
    intro g
    rw [hδ, mul_inv_eq_one, Units.ext_iff, Units.val_pow_eq_pow_val, hcU, MonoidHom.coe_toHomUnits]
  have hval : ∀ g, ((δ g : (PadicAlgCl l)ˣ) : PadicAlgCl l) = κ g * ((cU g⁻¹ : (PadicAlgCl l)ˣ) : PadicAlgCl l) ^ n := by
    intro g
    rw [hδ, map_inv, ← inv_pow, Units.val_mul, Units.val_pow_eq_pow_val, MonoidHom.coe_toHomUnits]
  have hcont : Continuous fun g => ((δ g : (PadicAlgCl l)ˣ) : PadicAlgCl l) := by
    simp_rw [hval, hcU]
    exact hκc.mul (((halg.comp (Units.continuous_val.comp (continuous_cycZ ℚ Ω l))).comp continuous_inv).pow n)
  have hδ1 : ∀ h, κ h = 1 → cycZ ℚ Ω l h = 1 → δ h = 1 := by
    intro h h1 h2
    rw [hker, h1, h2]
    simp
  have hN : ∀ A : ValuationSubring Ω, ∀ g ∈ Ine (F := ℚ) A, δ g ^ M = 1 := by
    intro A g hg
    by_cases hA : Raw.Away D.T A
    · rw [← map_pow]
      have hgM : g ^ M ∈ Ine (F := ℚ) A := Subgroup.pow_mem _ hg M
      have hr : g ^ M ∈ D.rbar.ker := (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp (hM g)).1).1
      refine hδ1 _ (hU A hA _ hgM hr) ?_
      have hlA : ¬ A.valuation (l : Ω) < 1 := hA l (by unfold Raw.T; simp)
      exact (places ℚ Ω l A).2.2.2 hlA hgM
    · have hA' : ∃ p ∈ D.T, A.valuation (p : Ω) < 1 := by
        unfold Raw.Away at hA
        push_neg at hA
        exact hA
      obtain ⟨p, hpT, hpA⟩ := hA'
      have hpT' : p = l ∨ p ∈ D.Sb := by
        unfold Raw.T at hpT
        simpa using hpT
      have hp : p.Prime := by
        rcases hpT' with rfl | hpS
        · exact Fact.out
        · exact (hF.1 p hpS).1
      obtain ⟨x, hx⟩ := (B3.placesQ Ω).2.2 p (D.pl p) A hp (hD.pl_over p hp) hpA
      have hconj : δ g ^ M = δ ((x⁻¹ * g * x) ^ M) := by
        rw [map_pow, map_mul, map_mul, map_inv]
        congr 1
        rw [mul_comm (δ x)⁻¹ (δ g), mul_assoc, inv_mul_cancel, mul_one]
      rw [hconj]
      have hI : (x⁻¹ * g * x) ^ M ∈ Ine (F := ℚ) (D.pl p) := Subgroup.pow_mem _ (hx g hg) M
      have hm := hM (x⁻¹ * g * x)
      have hψ : (x⁻¹ * g * x) ^ M ∈ D.ψ.ker := (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hm).1).2
      have ho : (x⁻¹ * g * x) ^ M ∈ D.om.ker := (Subgroup.mem_inf.mp hm).2
      rcases hpT' with rfl | hpS
      · exact (hker _).mpr (hl _ (Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨hI, hψ⟩, ho⟩))
      · refine hδ1 _ (hSb p hpS _ (Subgroup.mem_inf.mpr ⟨hI, hψ⟩)) ?_
        have hne : p ≠ l := (hF.1 p hpS).2.1
        have hnl : ¬ (D.pl p).valuation (l : Ω) < 1 := two (D.pl p) p l hp Fact.out hne (hD.pl_over p hp)
        exact (places ℚ Ω l (D.pl p)).2.2.2 hnl hI
  refine ⟨δ.ker, open_ker δ hcont M hM0 hN, fun g hg => (hker g).mp hg⟩
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

section SlopeTestRemainingChoices

variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l}

private theorem ps_wt_any {D : Raw Ω c} (h : D.Good) {A : ValuationSubring Ω} (hA : A.valuation (l : Ω) < 1) (i : Fin 4)
    {s : G ℚ Ω} (hs : s ∈ Ine (F := ℚ) A) (h1 : s ∈ D.ψ.ker) (h2 : s ∈ D.om.ker) :
    D.ps i s = chiO ℚ Ω l c.O s ^ D.wts4 i := by
  have hl : l.Prime := Fact.out
  obtain ⟨u, -, hu⟩ := (UpperTheory.V.Chr.placesQ Ω).2.2 l A _ hl hA (h.pl_over l hl)
  have e : ∀ γ : G ℚ Ω →* c.Oˣ, γ (u⁻¹ * s * u) = γ s := fun γ => by
    rw [map_mul, map_mul, map_inv, mul_right_comm, inv_mul_cancel, one_mul]
  have h3 := (facts D h).2.2.2.1 i (u⁻¹ * s * u) ⟨⟨hu s hs, (e _).trans h1⟩, (e _).trans h2⟩
  rwa [e, e] at h3

private theorem map_psi {ι Γ R R' : Type} [Group Γ] [CommRing R] [CommRing R'] (P : PD ι Γ R) (f : R →+* R') (v : ι) (i : Fin 4)
    (s : Γ) : (P.map f).ψ v i s = f (P.ψ v i s) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp [PD.ψ, PD.map, Matrix.mul_apply, adj_apply, map_sum]

private theorem charpoly_conj {H K K' : Type} [Group H] [Field K] [Field K'] (f : K →+* K') {r r' : H →* M4 K}
    (h : IsConj4 r r') (g : H) : (mapRep f r g).charpoly = (mapRep f r' g).charpoly := by
  obtain ⟨u, hu⟩ := h
  show ((r g).map f).charpoly = ((r' g).map f).charpoly
  rw [Matrix.charpoly_map, Matrix.charpoly_map, hu, Matrix.coe_units_inv, Matrix.charpoly_units_conj]

end SlopeTestRemainingChoices

theorem UpperTheory.V.Ws.pur :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → ∀ (ι : PadicAlgCl l ≃+* ℂ) (𝔞 : Amb l) (e : 𝔞.K ≃+* PadicAlgCl l), 𝔞.IsZero e → ∀ r, ProMod D ι 𝔞 r → Pure ι (mapRep ((e : 𝔞.K →+* PadicAlgCl l).comp 𝔞.toK) r) := by
  intro Ω _ _ _ l _ c D hD ι 𝔞 e he r hr
  obtain ⟨T, c', h, X, J, y, r₁, -, -, hPM, hy, -, hJ, hconj, -, hres, hin⟩ := hr
  let f : 𝔞.V →+* PadicAlgCl l := (e : 𝔞.K →+* PadicAlgCl l).comp 𝔞.toK
  let y' : X.A →ₐ[c'.O] PadicAlgCl l :=
    { f.comp y with
      commutes' := fun x => by
        have h1 : y (algebraMap c'.O X.A x) = 𝔞.a c' x := DFunLike.congr_fun hy x
        exact (congrArg f h1).trans (he.1 c' x) }
  have hy' : ∀ x, y' x = f (y x) := fun _ => rfl
  have hw : T.Wts (fun i => 2 * D.wts4 i) (X.P.map (y' : X.A →+* PadicAlgCl l)) := by
    have hc : Continuous (resQ T.F) := UpperTheory.V.Af.continuous_restrictScalarsHom ℚ T.F Ω
    refine ⟨(D.ψ.ker ⊓ D.om.ker).comap (resQ T.F),
      (hD.psi_open.inter (facts D hD).2.2.2.2.2.2.2.2.2.2.2.2.1).preimage hc, fun v i s hs => ?_⟩
    have h1 : resQ T.F s ∈ Ine (F := ℚ) (T.pl v) := hs.2
    have h2 := ps_wt_any hD (T.ovl v) i h1 hs.1.1 hs.1.2
    have h3 : f (y (X.P.ψ v i s)) = ((D.ps i (resQ T.F s) : c.O) : PadicAlgCl l) :=
      (congrArg f (hin v i s hs.2)).trans (he.1 c _)
    have h4 : (GlobalTheory.GalOfCusp.cycBar T.F Ω l s : PadicAlgCl l) =
      ((chiO ℚ Ω l c.O (resQ T.F s) : c.O) : PadicAlgCl l) := rfl
    refine (congrArg (· ^ 2) ((map_psi X.P _ v i s).trans h3)).trans ?_
    rw [h2]
    have h5 : (2 * (D.wts4 i : ℤ)) = ((D.wts4 i * 2 : ℕ) : ℤ) := by push_cast; ring
    simp only [h5, zpow_natCast, Units.val_pow_eq_pow_val, h4, SubmonoidClass.coe_pow, pow_mul]
  have hp := hPM.pur y' (fun b hb => by rw [hy', hJ b hb, map_zero]) hw (mapRep f r₁) (by
    ext g i j
    exact congrArg f (congrFun (congrFun (DFunLike.congr_fun hres g) i) j))
  obtain ⟨H, M, hH, hM, hp⟩ := hp
  refine ⟨H, M, hH, hM, fun p h1 h2 A hA n σ hn hσ hF => ?_⟩
  have h3 : (mapRep f r σ).charpoly = (mapRep f r₁ σ).charpoly :=
    charpoly_conj (e : 𝔞.K →+* PadicAlgCl l) hconj σ
  rw [h3]
  exact hp p h1 h2 A hA n σ hn hσ hF
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem ptp_root {B V : Type} [CommRing B] [CommRing V] [IsLocalRing V] (f : B →+* V) {I : Ideal B}
    (hf : ∀ b ∈ I, f b ∈ maximalIdeal V) {q : B[X]} (hq : Pp.Dist I q) {v : V} (hv : q.eval₂ f v = 0) :
    v ∈ maximalIdeal V := by
  rw [hq.1.as_sum, eval₂_add, eval₂_pow, eval₂_X, eval₂_finsetSum, add_eq_zero_iff_eq_neg] at hv
  refine Ideal.IsPrime.mem_of_pow_mem inferInstance q.natDegree ?_
  rw [hv]
  refine neg_mem (Ideal.sum_mem _ fun n hn => ?_)
  rw [eval₂_mul, eval₂_C]
  exact Ideal.mul_mem_right _ _ (hf _ (hq.2 n (Finset.mem_range.1 hn)))

theorem UpperTheory.V.Ws.ptPair :
    CohomologyHyp → ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → ∀ (𝔞 : Amb l) r, VPt D 𝔞 r → ∃ u, KPair D 𝔞 r u := by
  intro _ Ω _ _ _ l _ c D hD 𝔞 r ⟨hs, R, _, _, _, ρ, y, hρ, hy, hm, hr⟩
  subst hr
  have hy' : ∀ a, y (algebraMap c.O R a) = 𝔞.a c a := fun a => DFunLike.congr_fun hy a
  obtain ⟨B, _, _, _, _, τ, hτ, ⟨x, hx⟩, z, hz⟩ := hρ.atL
  obtain ⟨-, -, -, -, -, hrev, hinj, -⟩ := facts D hD
  haveI : HenselianLocalRing B := GlobalTheory.henselianLocalRing_of_henselianRing B
  obtain ⟨h, P, H, hP, hI⟩ := Pp.genTri ((D.Ip l).subgroupOf (D.Gp l)) (fun i (g : D.Gp l) => (D.ps i g : c.O)) D.s0
    (D.th D.s0 : c.O) τ.hom x hD.decompSigma_mem.1.1 hinj (fun i => by rw [← hrev i]; rfl) (Units.ne_zero _) (hτ.1 _) hτ.2 hx
  let f : B →+* 𝔞.V := y.comp (z : B →+* R)
  obtain ⟨h', H'⟩ := Pp.triSpec _ P _ (𝔞.V.subtype.comp f) h (fun a ha => by
    rw [RingHom.mem_ker, map_eq_zero_iff _ (IsFractionRing.injective B (FractionRing B))] at ha
    rw [ha]
    exact zero_mem _) H
  obtain ⟨u, hu, U⟩ := Pp.triIwa 𝔞.V _ P f h' H'
  have hf : ∀ a, f (algebraMap c.O B a) = 𝔞.a c a := fun a => (congrArg y (z.commutes a)).trans (hy' a)
  have hfm : ∀ b ∈ maximalIdeal B, f b ∈ maximalIdeal 𝔞.V := fun b hb =>
    hm _ ((res_eq_zero_iff c.O R _).1 ((res_map z b).trans ((res_eq_zero_iff c.O B _).2 hb)))
  have e : ∀ s : D.Gp l, (τ.hom s).map f = mapRep y ρ.hom s := fun s => by
    have : (D.loc ρ l).hom s = ρ.hom s := rfl
    ext i j
    rw [mapRep_apply, ← this, ← hz]
    rfl
  refine ⟨u, Pp.smallFlag 𝔞 _ u hs, fun g i j => ?_, fun g => ?_, fun A hA g hg hb => ?_, fun p hp g hg => ?_, hu,
    fun s hs => ?_, fun s hs i => ?_, fun s hs i => ?_⟩
  · rw [mapRep_apply, ← hy', ← map_sub]
    refine hm _ ((res_eq_zero_iff c.O R _).1 ?_)
    rw [map_sub, ρ.red, AlgHom.commutes]
    exact sub_self _
  · have h1 := hρ.mult g
    unfold IsGSp at h1 ⊢
    show adj ((ρ.hom g).map y) * (ρ.hom g).map y = _
    rw [(grp R).2.2.2.2.2.1, ← Matrix.map_mul, h1, ← hy']
    ext i j
    rw [Matrix.map_apply, Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul, map_mul, Matrix.one_apply,
      Matrix.one_apply, apply_ite y, map_one, map_zero]
  · show y.mapMatrix (ρ.hom g) = 1
    rw [hρ.unr A hA g hg hb, map_one]
  · obtain ⟨B', _, _, _, _, τ', hτ', -, z', hz'⟩ := hρ.atP p hp
    have h1 : ρ.hom g = (D.loc ρ p).hom ⟨g, hg.1.1⟩ := rfl
    show y.mapMatrix (ρ.hom g) = 1
    rw [h1, ← hz']
    show y.mapMatrix (z'.mapMatrix (τ'.hom _)) = 1
    rw [hτ'.2 _ hg, map_one, map_one]
  · have := (U ⟨s, hs⟩).1
    rwa [e] at this
  · obtain ⟨q, hq, hq'⟩ := hP ⟨s, hs⟩ i
    have := (U ⟨s, hs⟩).2 i
    rw [e, hq', eval₂_comp, eval₂_sub, eval₂_X, eval₂_C, hf] at this
    exact ptp_root f hfm hq this
  · have := (U ⟨s, hs.1⟩).2 i
    rw [e, hI _ hs, eval₂_sub, eval₂_X, eval₂_C, hf] at this
    exact sub_eq_zero.1 this
end
