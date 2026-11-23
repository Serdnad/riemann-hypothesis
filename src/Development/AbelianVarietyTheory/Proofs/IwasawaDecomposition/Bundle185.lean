module

public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LocalUnfoldingNonvanishingIffEventuallyNonzero
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.UnipotentCharacterArgumentMulStabilizer
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle078
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle061
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle069
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle070
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle001
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GlESymmApply
import Formalism.LocalToGlobal.GlobalTheory.GL6.PSplitT
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsVolumeTransportOfLatticeIsometry
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle180
import Formalism.LocalToGlobal.GlobalTheory.GL6.Statement

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.Col Formalism.L2.DIV GlobalTheory.QNormal GlobalTheory.Mem.Col2.IdxEx

noncomputable section

namespace GlobalTheory.Proof.hasLatticeNormalForm_of_between

open GlobalTheory.IndefiniteRowSideFullHecke.SandwichNormalForm GlobalTheory.Proof.normal_form_bounds_unfolding

section General

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n c : ℕ}

omit [StarRing E] in
theorem intV_eN (P : HeightOneSpectrum (𝓞 E)) (N s : ℕ) : IntV P (Loc.eN E N s) := by
  intro l
  unfold Loc.eN
  split_ifs
  · exact intAt_one P
  · exact IndefiniteRowSideFullHecke.SourceLatticeInvariance.intAt_zero P

theorem read_bounds (P : HeightOneSpectrum (𝓞 E)) (j : ℕ) (h ρ : (Fin (n + c) → E) ≃ₗ[E] (Fin (n + c) → E))
    (e : Fin c → ℤ) (z : Fin n → E) (hρ : ρ ∈ Loc.R1 E n c) (h1 : IntHom P h.symm.toLinearMap)
    (h2 : IntHom P (((qOf P : E) ^ j) • h.toLinearMap)) (hL : (ρ * h) '' {v | IntV P v} = nfLat P n c e z) :
    (∀ i, -(j : ℤ) ≤ e i ∧ e i ≤ 0) ∧ (1 ≤ c → IntV P z) := by
  have hq := Proof.NormalFormAtPrime.qOf_ne_zero P
  have hmem : ∀ v, IntV P v → ρ v ∈ nfLat P n c e z := fun v hv => by
    rw [← hL]
    refine ⟨h.symm v, h1 v hv, ?_⟩
    change ρ (h (h.symm v)) = ρ v
    rw [h.apply_symm_apply]
  refine ⟨fun i => ⟨?_, ?_⟩, fun hc a => ?_⟩
  · obtain ⟨v, hv, hrv⟩ : nfGen (qOf P) n c e z i ∈ (ρ * h) '' {v | IntV P v} := hL ▸ nfGen_mem P e z i
    change ρ (h v) = _ at hrv
    have hU : h v ∈ Loc.Ufl E n c (i.1 + 1) := by
      have := hρ.2.1 _ _ (hrv ▸ nfGen_mem_Ufl (qOf P) e z i)
      change ρ.symm (ρ (h v)) ∈ _ at this
      rwa [ρ.symm_apply_apply] at this
    have h3 : h v (Fin.natAdd n i) = (qOf P : E) ^ e i := by
      rw [← atN_natAdd (h v) i, ← atN_of_R1cond hρ.1 hU, hrv, atN_natAdd, nfGen_natAdd, if_pos rfl]
    have h4 : IntAt P ((qOf P : E) ^ j * h v (Fin.natAdd n i)) := h2 v hv (Fin.natAdd n i)
    rw [h3, ← zpow_natCast, ← zpow_add₀ hq] at h4
    have := nonneg_of_intAt_zpow h4
    omega
  · have hc : 1 ≤ c := by have := i.2; omega
    obtain ⟨u, hu, h'⟩ := (coords_of_mem hc (hmem _ (intV_eN P (n + c) (n + i.1)))).1 i
    refine le_of_zpow_eq hu ?_
    rw [← h', ← atN_natAdd (ρ _) i, atN_of_R1cond hρ.1 (eN_mem_Ufl (by omega)), atN_natAdd]
    simp [Loc.eN]
  · have h3 := (coords_of_mem hc (hmem _ (intV_eN P (n + c) n))).2 a
    have h4 : Loc.eN E (n + c) n (Fin.castAdd c a) = 0 := by
      unfold Loc.eN
      rw [if_neg (by have := a.2; simp; omega)]
    have h5 : Loc.eN E (n + c) n (Fin.natAdd n ⟨0, hc⟩) = 1 := by simp [Loc.eN]
    rw [hρ.1.2.1, h4, h5, one_mul, zero_sub] at h3
    simpa using IndefiniteRowSideFullHecke.SourceLatticeInvariance.intAt_neg h3

theorem nfLat_of_eq_zero (P : HeightOneSpectrum (𝓞 E)) (hc : c = 0) (e : Fin c → ℤ) (z z' : Fin n → E) :
    nfLat P n c e z = nfLat P n c e z' := by
  subst hc
  simp [nfLat]

end General

theorem nf_of_between : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (j : ℕ) (P : HeightOneSpectrum (𝓞 X.E)), P ∉ Pr.vGs → ∀ (h ρ : AutY X R j) (e : Fin (cOf R j) → ℤ) (z : Sp X.E (R.N j)), ρ ∈ Loc.R1 X.E (R.N j) (cOf R j) → Between j P h → (ρ * h) '' {v | IntV P v} = GlobalTheory.IndefiniteRowSideFullHecke.SandwichNormalForm.nfLat P (R.N j) (cOf R j) e z → GlobalTheory.IndefiniteRowSideFullHecke.SandwichNormalForm.NF Pr j P (ρ * h) := by
  intro X Pr R j P hP h ρ e z hρ hb hL
  obtain ⟨he, hz⟩ := read_bounds P j h ρ e z hρ hb.1 hb.2 hL
  rcases Nat.eq_zero_or_pos (cOf R j) with hc | hc
  · exact ⟨e, 0, he, zero_mem _, by rw [lamYat_coe hP, hL, nfLat_of_eq_zero P hc e z 0]⟩
  · exact ⟨e, z, he, (mem_stdAt_iff _).2 (hz hc), by rw [lamYat_coe hP, hL]⟩

end GlobalTheory.Proof.hasLatticeNormalForm_of_between

end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.Col Formalism.L2.DIV GlobalTheory.QNormal GlobalTheory.Mem.Col2.IdxEx

namespace GlobalTheory.Proof.affine_eigenvalue_eq_one_of_boxSum_ne_zero

def periods {V K : Type} [AddCommGroup V] (f : V → K) : AddSubgroup V where
  carrier := {u | ∀ t, f (t + u) = f t}
  zero_mem' := fun t => by simp
  add_mem' := fun {a b} ha hb t => by rw [← add_assoc, hb, ha]
  neg_mem' := fun {a} ha t => by rw [← ha (t + -a)]; simp

theorem eigen_eq_one_of_reps {V K : Type} [AddCommGroup V] [Field K] [CharZero K] (f : V → K) (L : AddSubgroup V)
    (S : Finset V) (hf : ∀ v, ∀ u ∈ L, f (v + u) = f v) (hinj : ∀ s ∈ S, ∀ s' ∈ S, s - s' ∈ L → s = s')
    (hcov : ∀ v, f v ≠ 0 → ∃ s ∈ S, v - s ∈ L) (T : V ≃+ V) (b : V) (χ : K) (hT : ∀ t, f (T t + b) = χ * f t)
    (hS : ∑ s ∈ S, f s ≠ 0) : χ = 1 := by
  classical
  obtain ⟨t₀, -, ht₀⟩ := Finset.exists_ne_zero_of_sum_ne_zero hS
  have hsurj : ∀ v, ∃ t, T t + b = v := fun v => ⟨T.symm (v - b), by simp⟩
  have hχ : χ ≠ 0 := by
    rintro rfl
    obtain ⟨t, rfl⟩ := hsurj t₀
    exact ht₀ (by rw [hT, zero_mul])
  set M := periods f with hM
  have hMf : ∀ v, ∀ u ∈ M, f (v + u) = f v := fun v u hu => hu v
  have hLM : L ≤ M := fun u hu t => hf t u hu
  have hTM : ∀ u, T u ∈ M ↔ u ∈ M := fun u => by
    have e : ∀ t, f (T t + b + T u) = χ * f (t + u) := fun t => by
      rw [← hT, map_add (f := _)]; congr 1; abel
    constructor
    · intro h t
      apply mul_left_cancel₀ hχ
      rw [← e, hMf _ _ h, hT]
    · intro h v
      obtain ⟨t, rfl⟩ := hsurj v
      rw [e, hMf _ _ h, hT]
  have hmap : M.map (T : V →+ V) = M := by
    ext v
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact (hTM u).2 hu
    · intro hv
      exact ⟨T.symm v, (hTM _).1 (by simpa using hv), by simp⟩
  have hout : ∀ v : V, f (QuotientAddGroup.mk v : V ⧸ M).out = f v := fun v => by
    have h : -v + (QuotientAddGroup.mk v : V ⧸ M).out ∈ M := by
      rw [← QuotientAddGroup.eq]; simp
    simpa using hMf v _ h
  let S' : Finset V := S.image fun s => (QuotientAddGroup.mk s : V ⧸ M).out
  have hinj' : ∀ s ∈ S', ∀ s' ∈ S', s - s' ∈ M → s = s' := fun s hs s' hs' h => by
    obtain ⟨a, -, rfl⟩ := Finset.mem_image.1 hs
    obtain ⟨a', -, rfl⟩ := Finset.mem_image.1 hs'
    have := QuotientAddGroup.eq_iff_sub_mem.2 h
    simp only [QuotientAddGroup.out_eq'] at this
    rw [this]
  have hcov' : ∀ v, f v ≠ 0 → ∃ s ∈ S', v - s ∈ M := fun v hv => by
    obtain ⟨s, hs, e⟩ := hcov v hv
    refine ⟨_, Finset.mem_image_of_mem _ hs, ?_⟩
    rw [← QuotientAddGroup.eq_iff_sub_mem, QuotientAddGroup.out_eq', QuotientAddGroup.eq_iff_sub_mem]
    exact hLM e
  have i1 : M.relIndex L ≠ 0 := by rw [AddSubgroup.relIndex_eq_one.2 hLM]; exact one_ne_zero
  have i2 : L.relIndex M ≠ 0 :=
    boxSum_ne_zero_invariant_affineChange.relIndex_ne_zero_of_cover L M (S.image fun s => s - t₀) fun k hk => by
      obtain ⟨s, hs, e⟩ := hcov (t₀ + k) (by rwa [hMf _ _ hk])
      refine ⟨_, Finset.mem_image_of_mem _ hs, ?_⟩
      convert e using 1
      abel
  have h1 := (sum_coset_reps_ne_zero_iff_commensurable.sum_reps_ne_zero_iff V K f L M S S' i1 i2 hf hMf hinj hcov hinj' hcov').1 hS
  have h2 := sum_coset_reps_ne_zero_iff_commensurable.finsum_quot_eq f M M S' le_rfl (by simp) hMf hinj' hcov'
  rw [AddSubgroup.relIndex_self, Nat.cast_one, one_mul] at h2
  rw [← h2] at h1
  let e : V ⧸ M ≃ V ⧸ M := (QuotientAddGroup.congr M M T hmap).toEquiv.trans (Equiv.addRight (QuotientAddGroup.mk b))
  have he : ∀ c : V ⧸ M, f (e c).out = χ * f c.out := fun c => by
    obtain ⟨v, rfl⟩ := QuotientAddGroup.mk_surjective c
    have : e (QuotientAddGroup.mk v) = QuotientAddGroup.mk (T v + b) := rfl
    rw [this, hout, hout, hT]
  have h3 : ∑ᶠ c : V ⧸ M, f (e c).out = ∑ᶠ c : V ⧸ M, f c.out := finsum_comp_equiv (f := fun c : V ⧸ M => f c.out) e
  simp only [he] at h3
  rw [← mul_finsum] at h3
  exact mul_right_cancel₀ h1 (by rw [h3, one_mul])

theorem eigen_eq_one : ∀ (E : Type) [Field E] [NumberField E] (K : Type) [Field K] [CharZero K] (P : HeightOneSpectrum (𝓞 E)), GlobalTheory.IndefiniteRowSideFullHecke.SourceLatticeInvariance.DegOneUnram P → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (f : (ι → E) → K) (N : ℕ), FunBdd P N f → ∀ (T : (ι → E) ≃ₗ[E] (ι → E)) (b : ι → E) (χ : K), (∀ t, f (T t + b) = χ * f t) → boxSum P N N f ≠ 0 → χ = 1 := by
  intro E _ _ K _ _ P hP ι _ _ f N hf T b χ hT hS
  have hq := NormalFormAtPrime.qOf_ne_zero P
  have h3 := rationalFractions_represent_primeNormQuotient.valsQ_reps E P hP N N
  refine eigen_eq_one_of_reps f (boxSum_ne_zero_invariant_affineChange.lat P ι ((qOf P : E) ^ N)⁻¹)
    (Fintype.piFinset fun _ : ι => LocE.valsQ E (qOf P) N N) (fun v u hu => ?_) (fun s hs s' hs' h => ?_)
    (fun v hv => ?_) T.toAddEquiv b χ hT (right_ne_zero_of_mul hS)
  · have := hf.2 v (((qOf P : E) ^ N)⁻¹ • u) hu
    rwa [smul_smul, mul_inv_cancel₀ (pow_ne_zero _ hq), one_smul] at this
  · funext i
    exact h3.1 _ (Fintype.mem_piFinset.1 hs i) _ (Fintype.mem_piFinset.1 hs' i) (h i)
  · choose s hs hs' using fun i => h3.2 (v i) (hf.1 v hv i)
    exact ⟨s, Fintype.mem_piFinset.2 hs, hs'⟩

end GlobalTheory.Proof.affine_eigenvalue_eq_one_of_boxSum_ne_zero
end

section

noncomputable section

namespace GlobalTheory.LevelUnram

open Formalism.BasicNotions Formalism.L2.Forms Formalism.UG Formalism.L2.GlobalTheoryTheory.LocalLatticeBases NumberField IsDedekindDomain Matrix GlobalTheory.LevelHecke
open scoped TensorProduct

theorem exists_mul_eq {R : Type} [CommRing R] [IsDedekindDomain R] (P : Ideal R) (hP : P.IsPrime) (t : R)
    (ht : t ∈ P) (ht2 : t ∉ P ^ 2) (a : R) (ha : a ∈ P) : ∃ s b, s ∉ P ∧ s * a = t * b := by
  obtain ⟨I, hI⟩ : P ∣ Ideal.span {t} := by
    rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]; exact ht
  have hIP : ¬ I ≤ P := by
    intro h
    apply ht2
    rw [← Ideal.span_singleton_le_iff_mem, hI, sq]
    exact Ideal.mul_mono_right h
  obtain ⟨s, hs, hsP⟩ := SetLike.not_le_iff_exists.1 hIP
  have h1 : a * s ∈ Ideal.span {t} := by rw [hI]; exact Ideal.mul_mem_mul ha hs
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton.1 h1
  exact ⟨s, b, hsP, by rw [mul_comm, hb]⟩

variable {E : Type} [Field E] [NumberField E]

theorem absNorm_span_invol (s : 𝓞 E →+* 𝓞 E) (hs : ∀ x, s (s x) = x) (a : 𝓞 E) :
    Ideal.absNorm (Ideal.span {s a}) = Ideal.absNorm (Ideal.span {a}) := by
  let e : 𝓞 E ≃+* 𝓞 E := RingEquiv.ofRingHom s s (RingHom.ext hs) (RingHom.ext hs)
  let e' : 𝓞 E ≃ₐ[ℤ] 𝓞 E := AlgEquiv.ofRingEquiv (f := e) (fun n => by simp)
  rw [Ideal.absNorm_span_singleton, Ideal.absNorm_span_singleton]
  exact congrArg Int.natAbs (Algebra.norm_eq_of_algEquiv e' a)

theorem notMem_sq {ι : Type} [Fintype ι] (s : 𝓞 E →+* 𝓞 E) (hs : ∀ x, s (s x) = x) (a : 𝓞 E) (p : ℕ) (hp : p.Prime)
    (ha : a * s a = (p : 𝓞 E)) (hcard : 2 * Fintype.card ι = Module.finrank ℚ E) (P : ι → Ideal (𝓞 E))
    (hmax : ∀ i, (P i).IsMaximal) (hinj : Function.Injective P) (haP : ∀ i, a ∈ P i)
    (hN : ∀ i, Ideal.absNorm (P i) = p) (i : ι) (hsa : s a ∉ P i) : (p : 𝓞 E) ∉ P i ^ 2 := by
  classical
  intro hmem
  have hnorm : Ideal.absNorm (Ideal.span {a}) = p ^ Fintype.card ι := by
    have h1 : Ideal.absNorm (Ideal.span {a}) ^ 2 = (p ^ Fintype.card ι) ^ 2 := by
      rw [← pow_mul, mul_comm, hcard, ← RingOfIntegers.rank, ← Ideal.absNorm_span_natCast, ← ha,
        ← Ideal.span_singleton_mul_span_singleton, map_mul, absNorm_span_invol s hs, sq]
    exact Nat.pow_left_injective two_ne_zero h1
  have ha2 : a ∈ P i ^ 2 := by
    obtain ⟨y, m, hm, h⟩ := (hmax i).exists_inv hsa
    have h1 : a = y * (p : 𝓞 E) + m * a := by
      rw [← ha]
      linear_combination (-a) * h
    rw [h1]
    refine Ideal.add_mem _ (Ideal.mul_mem_left _ _ hmem) ?_
    rw [sq]
    exact Ideal.mul_mem_mul hm (haP i)
  have hcop : ∀ j k, j ≠ k → IsCoprime (P j) (P k) := fun j k hjk =>
    Ideal.isCoprime_iff_sup_eq.2 ((hmax j).coprime_of_ne (hmax k) (fun h => hjk (hinj h)))
  have hd1 : P i ^ 2 ∣ Ideal.span {a} := by
    rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
    exact ha2
  have hd2 : ∏ j ∈ Finset.univ.erase i, P j ∣ Ideal.span {a} := by
    refine Finset.prod_dvd_of_coprime (fun j _ k _ hjk => hcop j k hjk) ?_
    intro j _
    rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
    exact haP j
  have hc : IsCoprime (P i ^ 2) (∏ j ∈ Finset.univ.erase i, P j) :=
    IsCoprime.pow_left (IsCoprime.prod_right fun j hj => hcop i j (Finset.ne_of_mem_erase hj).symm)
  have hd := map_dvd Ideal.absNorm (hc.mul_dvd hd1 hd2)
  rw [hnorm, map_mul, map_pow, map_prod, hN i,
    Finset.prod_congr rfl (fun j _ => hN j), Finset.prod_const, ← pow_add,
    Nat.pow_dvd_pow_iff_le_right hp.one_lt] at hd
  have h3 := Finset.card_erase_add_one (Finset.mem_univ i)
  rw [Finset.card_univ] at h3
  omega

theorem finrank_E (D : D7) : 2 * D.R.f = Module.finrank ℚ D.host.E := by
  letI := D.host.cmStar
  have h1 := Module.finrank_mul_finrank ℚ D.host.F D.host.E
  have h2 : Module.finrank ℚ D.host.F = D.R.f := by
    rw [D.host.finrank_hostF, Ranks.f, Ranks.n]
  rw [D.sp.cm.deg2, h2] at h1
  omega

theorem unram (D : D7) (u : D.what₂.Word) (A : AtTTied u) (v : (D.mem u).A.vT) :
    Unram (A.res v) (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) := by
  let s : 𝓞 D.host.E →+* 𝓞 D.host.E := RingOfIntegers.mapRingHom (sigD D : D.host.E →+* D.host.E)
  have hsc : ∀ x, (s x : D.host.E) = D.host.conj (x : D.host.E) := fun x => forms_involution_eq_host_conj _
  have hs : ∀ x, s (s x) = x := fun x => RingOfIntegers.ext (by rw [hsc, hsc, host_conj_involutive])
  have ha : A.piU * s A.piU = (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) := by
    apply RingOfIntegers.ext
    have := A.piU_norm
    rw [← hsc] at this
    simpa using this
  have hT0 : A.res v (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) = 0 := by
    rw [← ha, map_mul, A.res_pi, zero_mul]
  have h2 := notMem_sq s hs A.piU _ (D.mem u).A.T_prime ha (by rw [(D.mem u).A.card_vT]; exact finrank_E D)
    (fun w => RingHom.ker (A.res w)) (fun w => RingHom.ker_isMaximal_of_surjective _ (A.res_surj w))
    (fun w w' h => by
      apply A.eV.injective
      apply Subtype.ext
      apply HeightOneSpectrum.ext
      ext x
      have h' : RingHom.ker (A.res w) = RingHom.ker (A.res w') := h
      rw [A.res_v, A.res_v, ← RingHom.mem_ker, ← RingHom.mem_ker, h'])
    (fun w => A.res_pi w)
    (fun w => by
      rw [Ideal.absNorm_apply, Submodule.cardQuot_apply,
        Nat.card_congr (RingHom.quotientKerEquivOfSurjective (A.res_surj w)).toEquiv, Nat.card_eq_fintype_card,
        (D.mem u).A.card_Fv w])
    v (A.res_conj v _ (hsc _))
  exact ⟨hT0, fun a h => exists_mul_eq _ (RingHom.ker_isPrime _) _ hT0 h2 a h⟩

end GlobalTheory.LevelUnram

end
end

section

open Formalism.BasicNotions Formalism.L2.Forms Formalism.UG Formalism.L2.GlobalTheoryTheory.LocalLatticeBases NumberField IsDedekindDomain Matrix GlobalTheory.LevelHecke
open scoped TensorProduct

namespace GlobalTheory.LevelHecke.ValAt

section
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))}

theorem atV_mul {v : HeightOneSpectrum (𝓞 F)} {η η' : GA σ J} (h : AtV v η) (h' : AtV v η') : AtV v (η * η') := by
  intro v' hv'
  rw [Subgroup.coe_mul, map_mul, h v' hv', h' v' hv', one_mul]

theorem atV_inv {v : HeightOneSpectrum (𝓞 F)} {η : GA σ J} (h : AtV v η) : AtV v η⁻¹ := by
  intro v' hv'
  rw [Subgroup.coe_inv, map_inv, h v' hv', inv_one]

theorem inv_loc {ι : Type} [Fintype ι] (S : StepLevel F E σ J T f bad) (emb : ι → E →+* ℂ)
    (v : HeightOneSpectrum (𝓞 F)) (hb : v ∉ bad) (g) (hg : g ∈ AdFun S emb) (x κ : GA σ J) (hκ : AtV v κ)
    (hU : bc (prV (E := E) v) κ.1 ∈ S.Uloc v) : g (x * κ) = g x := by
  have hm : κ.1 ∈ S.U := by
    refine (S.U_eq _).2 ⟨κ.2, fun v' => ?_⟩
    by_cases h : v' = v
    · subst h; exact hU
    · rw [hκ v' h]; exact Subgroup.one_mem _
  have hc : S.chi ⟨κ.1, hm⟩ = 1 := S.chi_triv _ (fun v' hv' => hκ v' (fun h => hb (h ▸ hv')))
  funext y
  have := hg 1 (Subgroup.one_mem _) x (x * κ) ⟨κ.1, hm⟩ (by rw [map_one, one_mul]; rfl) y y
    (fun τ => by simp [atInf])
  rw [this, hc, Units.val_one, one_mul]

theorem val_self {ι : Type} [Fintype ι] (S : StepLevel F E σ J T f bad) (emb : ι → E →+* ℂ)
    (v : HeightOneSpectrum (𝓞 F)) (hv : (T : 𝓞 F) ∈ v.asIdeal) {k : Type} [Field k]
    (p : GA σ J → Pr (𝓞 E) (Fin n → E) k) (hb : v ∉ bad) (hp : PMap S v hv p) (g) (hg : g ∈ AdFun S emb)
    (x η : GA σ J) (hη : AtV v η) : valAt v p g x (p (x * η)) = g (x * η) := by
  have h : ∃ η', AtV v η' ∧ p (x * η') = p (x * η) := ⟨η, hη, rfl⟩
  unfold valAt
  rw [dite_eq_left h]
  obtain ⟨h1, h2⟩ := h.choose_spec
  generalize h.choose = η0 at h1 h2
  have e : x * η = x * η0 * (η0⁻¹ * η) := by group
  rw [e]
  refine (inv_loc S emb v hb g hg _ _ (atV_mul (atV_inv h1) hη) ?_).symm
  exact (hp.2.1 (x * η0) _).1 (by rw [← e, h2])

end

theorem valAt_spec : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (T f : ℕ) (bad : Set (HeightOneSpectrum (𝓞 F))) (ι : Type) [Fintype ι] (S : StepLevel F E σ J T f bad) (emb : ι → E →+* ℂ) (v : HeightOneSpectrum (𝓞 F)) (hv : (T : 𝓞 F) ∈ v.asIdeal) (k : Type) [Field k] (p : GA σ J → Pr (𝓞 E) (Fin n → E) k), v ∉ bad → PMap S v hv p → ∀ g ∈ AdFun S emb, (∀ x η : GA σ J, AtV v η → valAt v p g x (p (x * η)) = g (x * η)) ∧ (∀ x η : GA σ J, AtV v η → valAt v p g (x * η) = valAt v p g x) ∧ ∀ (a : ℤ) (δ x : GA σ J) (q : Pr (𝓞 E) (Fin n → E) k), (a : k) ≠ 0 → IsDia S v hv a δ → valAt v p g x (q.dil (a : k)) = valAt v p (fun y => g (y * δ)) x q := by
  intro F E _ _ _ _ _ σ n J T f bad ι _ S emb v hv k _ p hb hp g hg
  have key := val_self S emb v hv p hb hp g hg
  refine ⟨key, fun x η hη => ?_, fun a δ x q ha hδ => ?_⟩
  · funext q
    by_cases h : ∃ η', AtV v η' ∧ p (x * η * η') = q
    · obtain ⟨η', h1, rfl⟩ := h
      rw [key _ _ h1, mul_assoc, key _ _ (atV_mul hη h1)]
    · have h' : ¬ ∃ η', AtV v η' ∧ p (x * η') = q := by
        rintro ⟨η', h1, h2⟩
        refine h ⟨η⁻¹ * η', atV_mul (atV_inv hη) h1, ?_⟩
        rw [← h2]; congr 1; group
      unfold valAt
      rw [dite_eq_right h, dite_eq_right h']
  · have hδv : AtV v δ := hδ.1
    by_cases h : ∃ η', AtV v η' ∧ p (x * η') = q
    · have hR : valAt v p (fun y => g (y * δ)) x q = g (x * h.choose * δ) := by
        unfold valAt
        rw [dite_eq_left h]
      obtain ⟨h1, h2⟩ := h.choose_spec
      rw [hR]
      generalize h.choose = η0 at h1 h2
      rw [← h2, ← hp.2.2 _ δ a hδ, mul_assoc, key _ _ (atV_mul h1 hδv)]
    · have h' : ¬ ∃ η', AtV v η' ∧ p (x * η') = q.dil (a : k) := by
        rintro ⟨η', h1, h2⟩
        refine h ⟨η' * δ⁻¹, atV_mul h1 (atV_inv hδv), ?_⟩
        have h3 := hp.2.2 (x * (η' * δ⁻¹)) δ a hδ
        have e : x * (η' * δ⁻¹) * δ = x * η' := by group
        rw [e, h2] at h3
        have h4 := congrArg (Pr.dil (a : k)⁻¹) h3
        rw [Pr.dil_dil, Pr.dil_dil, inv_mul_cancel₀ ha, Pr.dil_one, Pr.dil_one] at h4
        exact h4.symm
      unfold valAt
      rw [dite_eq_right h, dite_eq_right h']

end GlobalTheory.LevelHecke.ValAt
end

section

open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.GaugeFrameBasis

open GlobalTheory.VolTransport

theorem eq_conj {A : Type} [CommRing A] {M : ℕ} {T T' x y : Matrix (Fin M) (Fin M) A}
    (h : T * T' = 1) (k : x * T' = T' * y) : y = T * x * T' := by
  rw [Matrix.mul_assoc, k, ← Matrix.mul_assoc, h, Matrix.one_mul]

theorem conj_rel {A : Type} [CommRing A] {M : ℕ} {T T' : Matrix (Fin M) (Fin M) A}
    (h : T' * T = 1) (x : Matrix (Fin M) (Fin M) A) : x * T' = T' * (T * x * T') := by
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, h, Matrix.one_mul]

theorem frame_basis : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R] [LocallyCompactSpace R] [SecondCountableTopology R] [MeasurableSpace R] [BorelSpace R], ∀ (M : ℕ) (J J' : Matrix (Fin M) (Fin M) E) (P : GL (Fin M) E), J' = Formalism.UG.cT (σ : E →+* E) (P : Matrix (Fin M) (Fin M) E) * J * (P : Matrix (Fin M) (Fin M) E) → (∃! e : HA R σ J ≃* HA R σ J', ∀ g, FrameRelR R σ J J' (P : Matrix (Fin M) (Fin M) E) g (e g)) ∧ ∀ e : HA R σ J ≃* HA R σ J', (∀ g, FrameRelR R σ J J' (P : Matrix (Fin M) (Fin M) E) g (e g)) → Continuous e ∧ Continuous e.symm := by
  intro F E _ _ _ _ _ σ R _ _ _ _ _ _ _ _ _ M J J' P hJ
  have h0 : IsoPair (σ : E →+* E) J J' ((P⁻¹ : GL (Fin M) E) : Matrix (Fin M) (Fin M) E)
      (P : Matrix (Fin M) (Fin M) E) := by
    refine ⟨Units.inv_mul P, Units.mul_inv P, ?_, hJ.symm⟩
    rw [hJ]
    calc _ = Formalism.UG.cT (σ : E →+* E) ((P : Matrix (Fin M) (Fin M) E) * ((P⁻¹ : GL (Fin M) E) : Matrix (Fin M) (Fin M) E)) * J *
          ((P : Matrix (Fin M) (Fin M) E) * ((P⁻¹ : GL (Fin M) E) : Matrix (Fin M) (Fin M) E)) := by
          rw [Formalism.UG.cT_mul]; simp only [Matrix.mul_assoc]
      _ = J := by rw [Units.mul_inv, Formalism.UG.cT_one, Matrix.one_mul, Matrix.mul_one]
  have h : IsoPair (sigR R σ) (JR R J) (JR R J')
      (((P⁻¹ : GL (Fin M) E) : Matrix (Fin M) (Fin M) E).map (inclR (F := F) R))
      ((P : Matrix (Fin M) (Fin M) E).map (inclR (F := F) R)) :=
    h0.map (inclR (F := F) R) (fun _ => rfl)
  let e0 : HA R σ J ≃* HA R σ J' := conjE h
  have hm : ∀ g, ((HA.mat R σ J' (e0 g) : GL _ _) : Matrix (Fin M) (Fin M) (R ⊗[F] E)) =
      ((P⁻¹ : GL (Fin M) E) : Matrix (Fin M) (Fin M) E).map (inclR (F := F) R) *
        ((HA.mat R σ J g : GL _ _) : Matrix (Fin M) (Fin M) (R ⊗[F] E)) *
        (P : Matrix (Fin M) (Fin M) E).map (inclR (F := F) R) := fun _ => rfl
  have hu : ∀ e : HA R σ J ≃* HA R σ J',
      (∀ g, FrameRelR R σ J J' (P : Matrix (Fin M) (Fin M) E) g (e g)) → e = e0 := by
    intro e he
    ext g
    apply Subtype.ext
    apply Units.ext
    refine Eq.trans ?_ (hm g).symm
    exact eq_conj h.1 (he g)
  refine ⟨⟨e0, fun g => ?_, hu⟩, fun e he => ?_⟩
  · exact conj_rel h.2.1 _
  · rw [hu e he]
    have : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
    exact ⟨conjU_continuous h, conjU_continuous h.symm⟩

end GlobalTheory.GaugeFrameBasis
end
