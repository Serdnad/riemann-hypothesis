module

public import Formalism.LocalToGlobal.KernelLattices.ThDistC
public import Formalism.LocalToGlobal.KernelLattices.XiIndCClass
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.EmbHInjective
import Mathlib.Algebra.AffineMonoid.Basic
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle086
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle011

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.MainNotions Formalism.L2.Th1.H GlobalTheory.ThetaMove GlobalTheory.IndefiniteRowSideFullHecke.IndexExponentDegree

noncomputable section

namespace GlobalTheory.PeriodIdealUnit

theorem not_dvd_different {K E : Type} [Field K] [NumberField K] [Field E] [NumberField E] [Algebra K E] {l : ℕ} (hl : l.Prime)
    (v : Ideal (𝓞 E)) [hvp : v.IsPrime] (hv : ((l : ℕ) : 𝓞 E) ∈ v) (h2 : ((l : ℕ) : 𝓞 E) ∉ v ^ 2) :
    ¬ v ∣ differentIdeal (𝓞 K) (𝓞 E) := by
  have hp : Prime (l : ℤ) := Nat.prime_iff_prime_int.mp hl
  have hmax : (Ideal.span {(l : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
  have hmap : Ideal.map (algebraMap ℤ (𝓞 E)) (Ideal.span {(l : ℤ)}) = Ideal.span {((l : ℕ) : 𝓞 E)} := by
    rw [Ideal.map_span]; simp
  have hle : Ideal.map (algebraMap ℤ (𝓞 E)) (Ideal.span {(l : ℤ)}) ≤ v := by
    rw [hmap, Ideal.span_le]; simpa using hv
  have : v.LiesOver (Ideal.span {(l : ℤ)}) :=
    ⟨hmax.eq_of_le (Ideal.comap_ne_top _ hvp.ne_top) (Ideal.map_le_iff_le_comap.mp hle)⟩
  have hb : Ideal.span {(l : ℤ)} ≠ ⊥ := by simpa using hl.ne_zero
  have he : v.ramificationIdx ℤ = 1 := by
    rw [← Ideal.ramificationIdx'_eq_ramificationIdx (Ideal.span {(l : ℤ)}) v hb]
    by_contra hne
    rw [← ne_eq, Ideal.ramificationIdx'_ne_one_iff hle, hmap, Ideal.span_le] at hne
    exact h2 (by simpa using hne)
  have : Algebra.IsUnramifiedAt ℤ v := Ideal.ramificationIdx_eq_one_iff.1 he
  exact not_dvd_differentIdeal_iff.2 (Algebra.IsUnramifiedAt.of_restrictScalars ℤ v)

theorem locP_eq_one {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) (I : Submodule (𝓞 E) E)
    (h1 : I ≤ localization₂ P.asIdeal (1 : Submodule (𝓞 E) E)) (h2 : ∃ n, n ∉ P.asIdeal ∧ n • (1 : E) ∈ I) :
    localization₂ P.asIdeal I = localization₂ P.asIdeal (1 : Submodule (𝓞 E) E) :=
  le_antisymm ((ThetaMove.localization_mono P h1).trans (localization_localization₂ P _).le)
    ((ThetaMove.localization_mono P (Submodule.one_le.2 h2 : (1 : Submodule (𝓞 E) E) ≤ localization₂ P.asIdeal I)).trans (localization_localization₂ P _).le)

theorem b_ne_zero (D : D7) :
    ((D.host.𝔟 : Ideal (𝓞 D.host.E)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) ≠ 0 :=
  FractionalIdeal.coeIdeal_ne_zero.2 fun h => by
    have h3 := D.host.𝔟_spec.2
    simp [h] at h3

theorem one_mem_inv_b (D : D7) : (1 : D.host.E) ∈ D.host.AA0 := by
  refine (FractionalIdeal.mem_inv_iff (b_ne_zero D)).2 fun y hy => ?_
  rw [one_mul]; exact FractionalIdeal.coeIdeal_le_one hy

theorem locP_AA_eq_one : ∀ (X : Fields) (D : D7) (s : Seam D X) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ) (P : HeightOneSpectrum (𝓞 X.E)), (Ideal.absNorm P.asIdeal).Prime → ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 X.E) ∉ P.asIdeal ^ 2 → Nat.Coprime (Ideal.absNorm cc) (Ideal.absNorm P.asIdeal) → localization₂ P.asIdeal (ambOf s B χ cD).AA = localization₂ P.asIdeal (1 : Submodule (𝓞 X.E) X.E) := by
  intro X D s cc δ B χ cD P hp h2 hc
  let e : 𝓞 D.host.E ≃+* 𝓞 X.E := RingOfIntegers.mapRingEquiv s.iE.symm
  have he : ∀ x : 𝓞 D.host.E, algebraMap (𝓞 X.E) X.E (e x) = s.iE.symm (algebraMap _ D.host.E x) := fun x => rfl
  have := P.isPrime
  let v : Ideal (𝓞 D.host.E) := P.asIdeal.comap (e : 𝓞 D.host.E →+* 𝓞 X.E)
  have hvp : v.IsPrime := Ideal.comap_isPrime _ _
  have hmem : ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 X.E) ∈ P.asIdeal := Ideal.absNorm_mem _
  have hv1 : ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 D.host.E) ∈ v := by
    rw [Ideal.mem_comap, map_natCast]; exact hmem
  have hv2 : ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 D.host.E) ∉ v ^ 2 := fun h => by
    have h3 := Ideal.le_comap_pow (e : 𝓞 D.host.E →+* 𝓞 X.E) 2 h
    rw [Ideal.mem_comap, map_natCast] at h3
    exact h2 h3
  have hnd := not_dvd_different (K := D.host.K) hp v hv1 hv2
  have hnot : ¬ D.host.𝔟 ≤ v := fun hle => hnd (by
    rw [D.host.𝔟_spec.1]
    exact (Ideal.dvd_iff_le.2 hle).mul_right _)
  obtain ⟨z, hz, hzP⟩ := SetLike.not_le_iff_exists.1 hnot
  have hN : ((Ideal.absNorm cc : ℕ) : 𝓞 X.E) ∉ P.asIdeal := fun h => by
    have h3 : IsCoprime ((Ideal.absNorm cc : ℕ) : 𝓞 X.E) ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 X.E) := hc.cast
    obtain ⟨a, b, hab⟩ := h3
    exact P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2
      (hab ▸ P.asIdeal.add_mem (P.asIdeal.mul_mem_left _ h) (P.asIdeal.mul_mem_left _ hmem)))
  refine locP_eq_one P _ ?_ ?_
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨c, -, t, ht, rfl⟩
    obtain ⟨w, hw⟩ := (FractionalIdeal.mem_one_iff _).1
      ((FractionalIdeal.mem_inv_iff (b_ne_zero D)).1 ht _ (FractionalIdeal.mem_coeIdeal_of_mem _ hz))
    refine ⟨e z, hzP, Submodule.mem_one.2 ⟨e (algebraMap (𝓞 D.host.K) (𝓞 D.host.E) c * w), ?_⟩⟩
    rw [Algebra.smul_def, he, he, ← map_mul, map_mul (algebraMap _ D.host.E), hw]
    congr 1
    have : algebraMap (𝓞 D.host.E) D.host.E (algebraMap (𝓞 D.host.K) (𝓞 D.host.E) c) = ((c : D.host.K) : D.host.E) := rfl
    rw [this]
    ring
  · refine ⟨_, hN, Submodule.subset_span ⟨((Ideal.absNorm cc : ℕ) : 𝓞 D.host.K), Ideal.absNorm_mem cc, 1, one_mem_inv_b D, ?_⟩⟩
    have h1 : (((((Ideal.absNorm cc : ℕ) : 𝓞 D.host.K) : D.host.K)) : D.host.E) = ((Ideal.absNorm cc : ℕ) : D.host.E) :=
      map_natCast ((algebraMap D.host.K D.host.E).comp (algebraMap (𝓞 D.host.K) D.host.K)) _
    rw [h1, mul_one, map_natCast, Algebra.smul_def, map_natCast, mul_one]

end GlobalTheory.PeriodIdealUnit
end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.MainNotions Formalism.L2.Th1.H GlobalTheory.ThetaMove GlobalTheory.IndefiniteRowSideFullHecke.IndexExponentDegree

namespace GlobalTheory.ThetaMove.TwistSd

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}

omit [StarRing E] in
theorem mem_twO_iff (N : Submodule (𝓞 E) (Sp E n)) (c : ℕ) (e : HeightOneSpectrum (𝓞 E) → ℤ) (y : Sp E n) :
    y ∈ twist₂ N c e ↔ ∀ Q : HeightOneSpectrum (𝓞 E), ((c : E) ^ e Q)⁻¹ • y ∈ localization₂ Q.asIdeal N := by
  simp [twist₂, Submodule.mem_iInf]

omit [StarRing E] in
theorem zpow_smul_mem (M : Submodule (𝓞 E) (Sp E n)) (c : ℕ) {k : ℤ} (hk : 0 ≤ k) {y : Sp E n} (hy : y ∈ M) :
    ((c : E) ^ k) • y ∈ M := by
  obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hk
  have : ((c : E) ^ (m : ℤ)) • y = ((c : 𝓞 E) ^ m) • y := by
    rw [← algebraMap_smul E ((c : 𝓞 E) ^ m) y, map_pow, map_natCast, zpow_natCast]
  rw [this]
  exact M.smul_mem _ hy


omit [StarRing E] in
theorem isLattice_twO {N : Submodule (𝓞 E) (Sp E n)} (hN : Submodule.IsLattice E N) {c : ℕ} (hc : 0 < c)
    {e : HeightOneSpectrum (𝓞 E) → ℤ} (he : ∀ Q, -1 ≤ e Q ∧ e Q ≤ 1) : Submodule.IsLattice E (twist₂ N c e) := by
  have hcE : (c : E) ≠ 0 := by exact_mod_cast hc.ne'
  have h1 : ∀ x ∈ twist₂ N c e, (c : E) • x ∈ N := fun x hx => mem_of_locP fun Q => by
    have := zpow_smul_mem _ c (k := 1 + e Q) (by have := he Q; omega) ((mem_twO_iff N c e x).1 hx Q)
    rwa [smul_smul, zpow_add₀ hcE, zpow_one, mul_inv_cancel_right₀ (zpow_ne_zero _ hcE)] at this
  have h2 : ∀ x ∈ N, (c : E) • x ∈ twist₂ N c e := fun x hx => (mem_twO_iff N c e _).2 fun Q => by
    have := zpow_smul_mem _ c (k := 1 - e Q) (by have := he Q; omega) (mem_localization_of_mem Q hx)
    rwa [zpow_sub₀ hcE, zpow_one, div_eq_mul_inv, mul_comm, ← smul_smul] at this
  refine ⟨?_, ?_⟩
  · let f : Sp E n →ₗ[𝓞 E] Sp E n := ((c : E) • (LinearMap.id : Sp E n →ₗ[E] Sp E n)).restrictScalars (𝓞 E)
    have hf : Function.Injective f := fun x y h => smul_right_injective _ hcE h
    refine Submodule.fg_of_fg_map_injective f hf (Submodule.FG.of_le hN.fg ?_)
    rintro _ ⟨x, hx, rfl⟩
    exact h1 x hx
  · intro s hs hli
    exact (LinearIndependent.iff_fractionRing _ _).mp hli
theorem hStd_zpow_left (c : ℕ) (k : ℤ) (y x : Sp E n) :
    hStd E n (((c : E) ^ k) • y) x = hStd E n y (((c : E) ^ k) • x) := by
  rw [LinearMap.map_smulₛₗ₂, LinearMap.map_smul, map_zpow₀, map_natCast]

theorem isSdLat_twO {N : Submodule (𝓞 E) (Sp E n)} (hN : IsSdLat N) {c : ℕ} (hc : 0 < c)
    {e : HeightOneSpectrum (𝓞 E) → ℤ} (he : ∀ Q, -1 ≤ e Q ∧ e Q ≤ 1) (hodd : ∀ Q, e (conjPrime₂ Q) = -e Q) :
    IsSdLat (twist₂ N c e) := by
  have hcE : (c : E) ≠ 0 := by exact_mod_cast hc.ne'
  refine ⟨isLattice_twO hN.1 hc he, ?_⟩
  change dual (hStd E n) (twist₂ N c e) = twist₂ N c e
  apply le_antisymm
  · intro x hx
    rw [mem_dual] at hx
    refine (mem_twO_iff N c e x).2 fun Q' => ?_
    obtain ⟨Q, rfl⟩ : ∃ Q, Q' = conjPrime₂ Q := ⟨conjPrime₂ Q', (GlobalTheory.GO.UniExt.conjP_involutive Q').symm⟩
    rw [GlobalTheory.GO.UniExt.mem_localization_conj_iff hN.1.fg hN.2, hodd, zpow_neg, inv_inv]
    intro y hy
    have hy' : ((c : E) ^ e Q) • y ∈ localization₂ Q.asIdeal (twist₂ N c e) := by
      rwa [mem_localization_twist N hc he, smul_smul, inv_mul_cancel₀ (zpow_ne_zero _ hcE), one_smul]
    obtain ⟨t, ht, hty⟩ := hy'
    obtain ⟨r, hr⟩ := Submodule.mem_one.1 (hx _ hty)
    refine ⟨r, cO E t, fun h => ht (by rwa [mem_conjP, cO_cO] at h), ?_⟩
    rw [hr, ← hStd_zpow_left, hStd_osmul_left, ← algebraMap_smul E (cO E t) x, LinearMap.map_smul, smul_eq_mul]
  · intro x hx
    rw [mem_dual]
    intro y hy
    refine mem_of_locP fun Q' => ?_
    obtain ⟨Q, rfl⟩ : ∃ Q, Q' = conjPrime₂ Q := ⟨conjPrime₂ Q', (GlobalTheory.GO.UniExt.conjP_involutive Q').symm⟩
    have h1 := (mem_twO_iff N c e x).1 hx (conjPrime₂ Q)
    rw [GlobalTheory.GO.UniExt.mem_localization_conj_iff hN.1.fg hN.2, hodd, zpow_neg, inv_inv] at h1
    obtain ⟨r, s, hs, hrs⟩ := h1 _ ((mem_twO_iff N c e y).1 hy Q)
    rw [← hStd_zpow_left, smul_smul, mul_inv_cancel₀ (zpow_ne_zero _ hcE), one_smul] at hrs
    exact ⟨s, hs, Submodule.mem_one.2 ⟨r, by rw [← hrs, Algebra.smul_def]⟩⟩

theorem expS_conjP {S : Finset (HeightOneSpectrum (𝓞 E))} (hS : ∀ P ∈ S, conjPrime₂ P ∉ S) (Q : HeightOneSpectrum (𝓞 E)) :
    expS S (conjPrime₂ Q) = -expS S Q := by
  unfold expS
  rw [GlobalTheory.GO.UniExt.conjP_involutive]
  by_cases h : Q ∈ S
  · simp [h, hS Q h]
  · by_cases h' : conjPrime₂ Q ∈ S <;> simp [h, h']

theorem isSdLat_twO_expS : ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (n : ℕ) (N : Submodule (𝓞 E) (Sp E n)) (c : ℕ)
    (S : Finset (HeightOneSpectrum (𝓞 E))), (∀ P ∈ S, conjPrime₂ P ∉ S) → IsSdLat N → 0 < c →
    IsSdLat (twist₂ N c (expS S)) ∧ IsSdLat (twist₂ N c fun Q => -expS S Q) := by
  intro E _ _ _ n N c S hS hN hc
  refine ⟨isSdLat_twO hN hc (expS_bound S) (expS_conjP hS), isSdLat_twO hN hc (fun Q => ?_) fun Q => ?_⟩
  · have := expS_bound S Q
    omega
  · rw [expS_conjP hS]

end GlobalTheory.ThetaMove.TwistSd
end
