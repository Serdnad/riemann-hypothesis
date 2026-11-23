module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.ShaFamMono
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.Bundle001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Bundle007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.GaloisCohomologyLength.LengthH0GlobalEqLevelGroup
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Bundle008
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Bundle006
import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.EqZeroOfNegEq
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
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.NumberField.Cyclotomic.Galois
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Chr

private theorem val_modEq {N : ℕ} [NeZero N] {x : ZMod N} {a : ℕ} (h : x = (a : ZMod N)) : x.val ≡ a [MOD N] := by
  rw [← ZMod.natCast_eq_natCast_iff, ZMod.natCast_zmod_val, h]

private theorem unitsMap_val {g N : ℕ} [NeZero g] [NeZero N] (h : g ∣ N) (u : (ZMod N)ˣ) :
    ((ZMod.unitsMap h u : (ZMod g)ˣ) : ZMod g).val ≡ (u : ZMod N).val [MOD g] := by
  apply val_modEq
  rw [ZMod.unitsMap_val, ZMod.cast_eq_val]

private theorem down (P : ℕ → Prop) (g : ℕ) [NeZero g] (hP : ∀ a b, a ≡ b [MOD g] → (P a ↔ P b))
    (K : Subgroup (ZMod g)ˣ) (hK : ∀ u, u ∈ K ↔ P (u : ZMod g).val)
    (E : Type) [Field E] [NumberField E] (N : ℕ) [NeZero N] (h : g ∣ N)
    (j : E →ₐ[ℚ] CyclotomicField N ℚ) (ζ : CyclotomicField N ℚ) (hζ : IsPrimitiveRoot ζ N)
    (hj : ∀ (τ : CyclotomicField N ℚ ≃ₐ[ℚ] CyclotomicField N ℚ) (a : ℕ), τ ζ = ζ ^ a →
      ((∀ x : E, τ (j x) = j x) ↔ P a)) : HasLevel E g K := by
  refine ((levChange E N).2 g h K).2 ⟨j, ζ, hζ, fun τ u hu => ?_⟩
  rw [hj τ _ hu, Subgroup.mem_comap, hK]
  exact (hP _ _ (unitsMap_val h u)).symm

private theorem exists_sub (P : ℕ → Prop) (g : ℕ) [NeZero g] (hP : ∀ a b, a ≡ b [MOD g] → (P a ↔ P b))
    (h1 : P 1) (hm : ∀ a b, P a → P b → P (a * b)) :
    ∃ K : Subgroup (ZMod g)ˣ, ∀ u, u ∈ K ↔ P (u : ZMod g).val := by
  let S : Submonoid (ZMod g)ˣ :=
    { carrier := {u | P (u : ZMod g).val}
      one_mem' := (hP _ _ (val_modEq (a := 1) (by simp))).2 h1
      mul_mem' := fun {u v} hu hv =>
        (hP _ _ (val_modEq (a := (u : ZMod g).val * (v : ZMod g).val) (by simp))).2 (hm _ _ hu hv) }
  refine ⟨{ S with inv_mem' := fun {u} hu => ?_ }, fun u => Iff.rfl⟩
  have : u⁻¹ ∈ Submonoid.powers u := mem_powers_iff_mem_zpowers.2 (inv_mem (Subgroup.mem_zpowers u))
  exact (Submonoid.powers_le (P := S)).2 hu this

private theorem ker_congr (A : AbF) {a b : ℕ} (h : a ≡ b [MOD A.m]) : A.ker a ↔ A.ker b := by
  unfold AbF.ker
  rw [(ZMod.natCast_eq_natCast_iff _ _ _).2 h]

private theorem pm_iff (n a : ℕ) : (a ≡ 1 [MOD n] ∨ a + 1 ≡ 0 [MOD n]) ↔ ((a : ZMod n) = 1 ∨ (a : ZMod n) = -1) := by
  rw [← ZMod.natCast_eq_natCast_iff, ← ZMod.natCast_eq_natCast_iff]
  push_cast
  rw [add_eq_zero_iff_eq_neg]

private theorem jac_congr {a b q : ℕ} (h : a ≡ b [MOD q]) : jacobiSym (a : ℤ) q = jacobiSym (b : ℤ) q :=
  jacobiSym.mod_left' (Int.natCast_modEq_iff.2 h)

theorem UpperTheory.V.Chr.abLevel :
    (∀ (A : AbF) (E : Type) [Field E] [NumberField E], IsAbField A E → HasLevel E A.m A.H) ∧
          ∀ (A : AbF) (e q d : ℕ) (E : Type) [Field E] [NumberField E], IsCompField A e q d E → ∀ (N : ℕ) [NeZero N], 2 ^ (e + 2) ∣ N → A.m ∣ N → q ∣ N → d ∣ N →
            ∃ H : Subgroup (ZMod N)ˣ, HasLevel E N H ∧ ∀ (u : (ZMod N)ˣ) (a : ℕ), (u : ZMod N) = (a : ZMod N) →
              (u ∈ H ↔ (a ≡ 1 [MOD 2 ^ (e + 2)] ∨ a + 1 ≡ 0 [MOD 2 ^ (e + 2)]) ∧ A.ker a ∧ jacobiSym (a : ℤ) q = 1 ∧ jacobiSym (a : ℤ) d = 1) := by
  refine ⟨?_, ?_⟩
  · rintro A E _ _ ⟨N, _, j, ζ, h, hζ, hj⟩
    refine down A.ker A.m (fun a b => ker_congr A) A.H (fun u => ?_) E N h j ζ hζ hj
    unfold AbF.ker
    rw [ZMod.natCast_zmod_val]
    exact ⟨fun hu => ⟨u, hu, rfl⟩, fun ⟨v, hv, e⟩ => Units.ext e ▸ hv⟩
  · rintro A e q d E _ _ ⟨M, _, j, ζ, a1, a2, a3, a4, hζ, hj⟩ N _ b1 b2 b3 b4
    haveI : NeZero (Nat.gcd M N) := ⟨(Nat.gcd_pos_of_pos_left _ (NeZero.pos M)).ne'⟩
    let P : ℕ → Prop := fun a => (a ≡ 1 [MOD 2 ^ (e + 2)] ∨ a + 1 ≡ 0 [MOD 2 ^ (e + 2)]) ∧ A.ker a ∧
      jacobiSym (a : ℤ) q = 1 ∧ jacobiSym (a : ℤ) d = 1
    have hP : ∀ a b, a ≡ b [MOD Nat.gcd M N] → (P a ↔ P b) := fun a b h => by
      simp only [P]
      rw [pm_iff, pm_iff, (ZMod.natCast_eq_natCast_iff _ _ _).2 (h.of_dvd (Nat.dvd_gcd a1 b1)),
        ker_congr A (h.of_dvd (Nat.dvd_gcd a2 b2)), jac_congr (h.of_dvd (Nat.dvd_gcd a3 b3)),
        jac_congr (h.of_dvd (Nat.dvd_gcd a4 b4))]
    have h1 : P 1 := ⟨Or.inl (Nat.ModEq.refl _), ⟨1, A.H.one_mem, by simp⟩, by simp, by simp⟩
    have hm : ∀ a b, P a → P b → P (a * b) := by
      rintro a b ⟨p1, ⟨u, hu, eu⟩, p3, p4⟩ ⟨r1, ⟨v, hv, ev⟩, r3, r4⟩
      refine ⟨?_, ⟨u * v, A.H.mul_mem hu hv, by rw [Units.val_mul, eu, ev, Nat.cast_mul]⟩, ?_, ?_⟩
      · rw [pm_iff] at p1 r1 ⊢
        rw [Nat.cast_mul]
        rcases p1 with p | p <;> rcases r1 with r | r <;> simp [p, r]
      · rw [Nat.cast_mul, jacobiSym.mul_left, p3, r3, mul_one]
      · rw [Nat.cast_mul, jacobiSym.mul_left, p4, r4, mul_one]
    obtain ⟨K, hK⟩ := exists_sub P _ hP h1 hm
    have hL := down P _ hP K hK E M (Nat.gcd_dvd_left M N) j ζ hζ hj
    refine ⟨_, ((levChange E N).2 _ (Nat.gcd_dvd_right M N) K).1 hL, fun u a hu => ?_⟩
    rw [Subgroup.mem_comap, hK]
    exact hP _ _ ((unitsMap_val _ u).trans ((val_modEq hu).of_dvd (Nat.gcd_dvd_right M N)))
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Chr

private theorem UpperTheory.V.Chr.layerLevel_emb (n : ℕ) [NeZero n] (K L C : Type) [Field K] [Field L] [Field C] [Algebra K L]
    [Algebra K C] [IsCyclotomicExtension {n} K L] (ζ : C) (hζ : IsPrimitiveRoot ζ n) : Nonempty (L →ₐ[K] C) := by
  haveI : Polynomial.IsSplittingField K L (Polynomial.X ^ n - 1) :=
    IsCyclotomicExtension.isSplittingField_X_pow_sub_one (n := n) (K := K) (L := L)
  have hs : Polynomial.Splits ((Polynomial.X ^ n - 1 : Polynomial K).map (algebraMap K C)) := by
    rw [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_one,
      ← Polynomial.C_1]
    exact Polynomial.X_pow_sub_one_splits hζ
  exact ⟨Polynomial.IsSplittingField.lift L _ hs⟩

theorem UpperTheory.V.Chr.layerLevel :
    ∀ (A : AbF) (l j : ℕ), l.Prime → ∀ (L₀ : Type) [Field L₀] [NumberField L₀] (L₁ : Type) [Field L₁] [NumberField L₁] [Algebra L₀ L₁],
          IsAbField A L₀ → IsLayer l j L₀ L₁ → ∃ (N : ℕ) (_ : NeZero N) (H : Subgroup (ZMod N)ˣ), HasLevel L₁ N H := by
  intro A l j hl L₀ _ _ L₁ _ _ _ hA hL
  obtain ⟨N, hN, jj, ζ, -, hζ, -⟩ := hA
  obtain ⟨⟨k, hk⟩, -⟩ := hL
  haveI : NeZero (l ^ k) := ⟨pow_ne_zero _ hl.ne_zero⟩
  haveI : NeZero ((N : ℕ) : ℚ) := ⟨by exact_mod_cast NeZero.ne N⟩
  haveI hN' : NeZero (N * l ^ k) := ⟨Nat.mul_ne_zero (NeZero.ne N) (pow_ne_zero _ hl.ne_zero)⟩
  haveI : NeZero (((N * l ^ k : ℕ)) : ℚ) := ⟨by exact_mod_cast NeZero.ne (N * l ^ k)⟩
  obtain ⟨r, hr⟩ := @IsCyclotomicExtension.exists_isPrimitiveRoot {N * l ^ k} ℚ
    (CyclotomicField (N * l ^ k) ℚ) _ _ _ (CyclotomicField.isCyclotomicExtension (N * l ^ k) ℚ)
    (N * l ^ k) rfl (NeZero.ne _)
  have hrN : IsPrimitiveRoot (r ^ (l ^ k)) N := by
    have h0 := hr.pow_of_dvd (pow_ne_zero k hl.ne_zero) (dvd_mul_left _ N)
    rwa [Nat.mul_div_cancel _ (pow_pos hl.pos k)] at h0
  have hrl : IsPrimitiveRoot (r ^ N) (l ^ k) := by
    have h0 := hr.pow_of_dvd (NeZero.ne N) (dvd_mul_right N _)
    rwa [Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero (NeZero.ne N))] at h0
  obtain ⟨g⟩ := @layerLevel_emb N _ ℚ (CyclotomicField N ℚ) (CyclotomicField (N * l ^ k) ℚ)
    _ _ _ _ _ (CyclotomicField.isCyclotomicExtension N ℚ) _ hrN
  letI : Algebra L₀ (CyclotomicField (N * l ^ k) ℚ) :=
    ((g : CyclotomicField N ℚ →+* CyclotomicField (N * l ^ k) ℚ).comp
      (jj : L₀ →+* CyclotomicField N ℚ)).toAlgebra
  obtain ⟨h1⟩ := layerLevel_emb (l ^ k) L₀ L₁ (CyclotomicField (N * l ^ k) ℚ) (r ^ N) hrl
  obtain ⟨H, hH⟩ := (levChange L₁ (N * l ^ k)).1
    ⟨(h1 : L₁ →+* CyclotomicField (N * l ^ k) ℚ).toRatAlgHom⟩
  exact ⟨N * l ^ k, hN', H, hH⟩
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Chr

theorem UpperTheory.V.Chr.factorGS :
    ∀ (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] (N : ℕ) [NeZero N] (e : ℕ) (ψ : G k Ω →* Oˣ), (cls k Ω N).ker ≤ ψ.ker →
          ∀ S : Set (HeightOneSpectrum (𝓞 k)), S = Above k (l * N) →
          ∃ θ : GS Ω S →* Oˣ, θ.comp (toGS Ω S) = (Psi l e ψ)⁻¹ ∧ ContAction (twist₂ l θ) := by
  intro k Ω _ _ _ _ _ l _ O _ _ _ _ _ N _ e ψ hker S hS
  have hψopen : IsOpen (ψ.ker : Set (G k Ω)) := Subgroup.isOpen_mono hker (clsFacts k Ω N).1
  have hcyc : IsClosed ((cycZ k Ω l).ker : Set (G k Ω)) := by
    rw [MonoidHom.coe_ker]
    exact isClosed_singleton.preimage (contTw k Ω l).1
  have hNS : NS Ω S ≤ ψ.ker ⊓ (cycZ k Ω l).ker := by
    unfold NS
    refine Subgroup.topologicalClosure_minimal _ ?_ ((Subgroup.isClosed_of_isOpen _ hψopen).inter hcyc)
    refine Subgroup.normalClosure_le_normal ?_
    intro σ hσ
    simp only [Set.mem_iUnion, Set.mem_setOf_eq] at hσ
    obtain ⟨v, hv, A, hA, hσ⟩ := hσ
    have hvS : v ∉ Above k (l * N) := by
      rw [← hS]
      exact hv
    have hmem : ∀ m : ℕ, m ∣ l * N → ¬ A.valuation (m : Ω) < 1 := by
      intro m hm hlt
      apply hvS
      have hx := (hA (m : 𝓞 k)).1 (by simpa using hlt)
      obtain ⟨c, hc⟩ := hm
      show ((l * N : ℕ) : 𝓞 k) ∈ v.asIdeal
      rw [hc, Nat.cast_mul]
      exact Ideal.mul_mem_right _ _ hx
    refine ⟨?_, ?_⟩
    · exact hker ((clsFacts k Ω N).2.2.2.2 A (hmem N (dvd_mul_left N l)) hσ)
    · exact (places k Ω l A).2.2.2 (hmem l (dvd_mul_right l N)) hσ
  have hP : NS Ω S ≤ (Psi l e ψ)⁻¹.ker := by
    intro σ hσ
    have h1 : ψ σ = 1 := (hNS hσ).1
    have h2 : cycZ k Ω l σ = 1 := (hNS hσ).2
    rw [MonoidHom.mem_ker]
    unfold Psi chiO
    simp [h1, h2]
  refine ⟨QuotientGroup.lift (NS Ω S) (Psi l e ψ)⁻¹ hP, MonoidHom.ext fun σ => rfl, ?_⟩
  have heq : (Psi l e ψ)⁻¹ = ψ⁻¹ * chiO k Ω l O ^ (-(e : ℤ)) := by
    unfold Psi
    rw [mul_inv, mul_comm, zpow_neg]
  have hopen : IsOpen ((ψ⁻¹).ker : Set (G k Ω)) := by
    convert hψopen using 2
    ext σ
    simp
  have hG := (contTw k Ω l).2.2 O ψ⁻¹ (-(e : ℤ)) hopen
  rw [← heq] at hG
  unfold ReciprocityTheory.Gal.ContAction at hG ⊢
  rw [← ((QuotientGroup.isOpenQuotientMap_mk (N := NS Ω S)).prodMap (IsOpenQuotientMap.id (X := QO l O))).continuous_comp_iff]
  exact hG
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Chr

private theorem cls_eq_of {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    {N : ℕ} [NeZero N] {ζ : Ω} (hζ : IsPrimitiveRoot ζ N) (σ : G k Ω) (u : (ZMod N)ˣ)
    (h : σ ζ = ζ ^ (u : ZMod N).val) : cls k Ω N σ = u := by
  have h1 := cls_spec N σ ζ hζ.pow_eq_one
  rw [h1] at h
  apply Units.ext
  exact ZMod.val_injective N (hζ.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) h)

private theorem aux (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (N : ℕ) [NeZero N]
    (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {N} ℚ K] :
    Function.Surjective (cls ℚ Ω N) ∧
      ∀ (l : ℕ) [Fact l.Prime] (A : ValuationSubring Ω), A.valuation (l : Ω) < 1 →
        KStar.TotallyRealRoots.princ l (N.factorization l) ≤ (Ine (F := ℚ) A ⊓ (cls ℚ Ω N).ker).map (cycZ ℚ Ω l) := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : Algebra.IsAlgebraic ℚ Ω := IsAlgClosure.isAlgebraic
  haveI : Normal ℚ Ω := IsAlgClosure.normal ℚ Ω
  let ι : K →ₐ[ℚ] Ω := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  letI : Algebra K Ω := ι.toRingHom.toAlgebra
  haveI : IsScalarTower ℚ K Ω := IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
  haveI : Algebra.IsAlgebraic K Ω := Algebra.IsAlgebraic.tower_top (K := ℚ) K
  haveI : IsAlgClosure K Ω := IsAlgClosure.mk ‹_› ‹_›
  have hζK := IsCyclotomicExtension.zeta_spec N ℚ K
  set ζ := IsCyclotomicExtension.zeta N ℚ K
  have hζ : IsPrimitiveRoot (algebraMap K Ω ζ) N :=
    hζK.map_of_injective (algebraMap K Ω).injective
  have hker : ∀ τ : G K Ω, cls ℚ Ω N (galEmb ℚ K Ω τ) = 1 := by
    intro τ
    apply cls_eq_of hζ
    have hτ : galEmb ℚ K Ω τ (algebraMap K Ω ζ) = algebraMap K Ω ζ := τ.commutes ζ
    rw [hτ, Units.val_one, ZMod.val_one_eq_one_mod]
    conv_lhs => rw [← pow_one (algebraMap K Ω ζ), ← Nat.mod_add_div 1 N, pow_add, pow_mul,
      hζ.pow_eq_one, one_pow, mul_one]
  refine ⟨?_, ?_⟩
  · intro u
    let χ : K ≃ₐ[ℚ] K := (IsCyclotomicExtension.Rat.galEquivZMod N K).symm u
    refine ⟨χ.liftNormal Ω, cls_eq_of hζ _ u ?_⟩
    rw [AlgEquiv.liftNormal_commutes,
      IsCyclotomicExtension.Rat.galEquivZMod_apply_of_pow_eq N K χ hζK.pow_eq_one]
    have hχ : IsCyclotomicExtension.Rat.galEquivZMod N K χ = u := MulEquiv.apply_symm_apply _ u
    rw [hχ, map_pow]
  · intro l _ A hA
    have hA' : A ≠ ⊤ := by
      intro h
      exact ((places K Ω l A).2.1 h).2 hA
    obtain ⟨v, hv⟩ := (places K Ω l A).1 hA'
    have hvl := ((places K Ω l A).2.2.1 v hv).mp hA
    have h1 := UpperTheory.V.LDataCardLeFinrank.princ_le_ineImage (F := K) (Ω := Ω) (N := N) (K := K)
      (AlgHom.id ℚ K) hvl hv
    refine h1.trans ?_
    unfold UpperTheory.V.LDataCardLeFinrank.ineImage
    have hfam := UpperTheory.V.Base.galEmbFam ℚ K Ω l
    rw [← hfam.2.2.1, ← Subgroup.map_map]
    apply Subgroup.map_mono
    rintro σ ⟨τ, hτ, rfl⟩
    refine ⟨?_, hker τ⟩
    have hI := (hfam.1 A).2
    rw [← hI] at hτ
    exact hτ

theorem UpperTheory.V.Chr.clsOnto :
    ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (N : ℕ) [NeZero N], Function.Surjective (cls ℚ Ω N) ∧
          ∀ (l : ℕ) [Fact l.Prime] (A : ValuationSubring Ω), A.valuation (l : Ω) < 1 →
            KStar.TotallyRealRoots.princ l (N.factorization l) ≤ (Ine (F := ℚ) A ⊓ (cls ℚ Ω N).ker).map (cycZ ℚ Ω l) := by
  intro Ω _ _ _ N _
  exact aux Ω N (CyclotomicField N ℚ)
end
