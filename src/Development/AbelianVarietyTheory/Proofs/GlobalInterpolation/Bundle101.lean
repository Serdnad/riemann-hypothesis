module

public import Formalism.LocalToGlobal.KernelLattices.ThDistC
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle048
public import Development.AutomorphicArithmetic.CyclotomicBounds.RamifiedDiscriminants.Bundle001
public import Development.AutomorphicArithmetic.CyclotomicBounds.Bundle003
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle017
public import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.IsSemiChar
public import Mathlib.Basic.Real.Basic
public import Mathlib.GroupTheory.Index
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
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
import Mathlib.RingTheory.Radical.NatInt
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
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.JetSumTable
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle082
import Formalism.HermitianLattices.Bundle001
import Formalism.LocalToGlobal.Columns.AlgebraMapMemMaximalIdealPowIff
import Formalism.LocalToGlobal.Divisibility.CoefMod
import Formalism.LocalToGlobal.KernelLattices.XiIndCClass
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Analysis.Complex.Circle

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.L2.Th1.H GlobalTheory.IndefiniteRowSideFullHecke.JetSumTable GlobalTheory.MomT

namespace GlobalTheory.AAUnitAway

theorem natCast_notMem {A : Type} [CommRing A] {I : Ideal A} (hI : I ≠ ⊤) {l n : ℕ} (hl : (l : A) ∈ I)
    (h : Nat.Coprime n l) : (n : A) ∉ I := by
  intro hn
  obtain ⟨x, y, e⟩ : IsCoprime (n : A) (l : A) := Nat.Coprime.cast h
  exact hI ((Ideal.eq_top_iff_one _).2 (e ▸ I.add_mem (I.mul_mem_left _ hn) (I.mul_mem_left _ hl)))

theorem exists_den (D : D7) (Q : Ideal (𝓞 D.host.E)) [hQ : Q.IsPrime] {l : ℕ} (hl : l.Prime) (h2 : l ∉ D.host.small) (hq : l ≠ D.host.q)
    (hlQ : (l : 𝓞 D.host.E) ∈ Q) :
    ∃ z : 𝓞 D.host.E, z ∉ Q ∧ ∀ t ∈ D.host.AA0, ∃ w : 𝓞 D.host.E, (w : D.host.E) = t * (z : D.host.E) := by
  have hnot : ¬ D.host.𝔟 ≤ Q := by
    intro hle
    have hd : Q ∣ differentIdeal (𝓞 D.host.K) (𝓞 D.host.E) := by
      rw [D.host.𝔟_spec.1]
      exact (Ideal.dvd_iff_le.2 hle).mul_right _
    exact natCast_notMem hQ.ne_top hlQ (Nat.Coprime.mul_left
      ((Nat.Prime.coprime_iff_not_dvd hl).2 (UpperTheory.Small.not_dvd_QS D.host hl h2)).symm
      ((Nat.coprime_primes D.host.hyp.1 hl).2 hq.symm)) (D.host.der.diffSupport Q hQ hd)
  obtain ⟨z, hz, hzP⟩ := Set.not_subset.1 hnot
  have hB : ((D.host.𝔟 : Ideal (𝓞 D.host.E)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.2 (Formalism.L2.Pj.b_ne_bot D)
  refine ⟨z, hzP, fun t ha => ?_⟩
  unfold Host.AA0 at ha
  rw [FractionalIdeal.mem_inv_iff hB] at ha
  obtain ⟨w, hw⟩ := (FractionalIdeal.mem_one_iff _).1 (ha _ ((FractionalIdeal.mem_coeIdeal _).2 ⟨z, hz, rfl⟩))
  exact ⟨w, hw⟩

theorem localization_le_of_le_localization₂ {E : Type} [Field E] [NumberField E] [StarRing E] (P : HeightOneSpectrum (𝓞 E)) {I J : Submodule (𝓞 E) E}
    (h : I ≤ localization₂ P.asIdeal J) : localization₂ P.asIdeal I ≤ localization₂ P.asIdeal J := by
  intro x hx
  obtain ⟨s, hs, hx⟩ := (mem_locP P I x).1 hx
  obtain ⟨t, ht, hx⟩ := (mem_locP P J _).1 (h hx)
  refine (mem_locP P J x).2 ⟨t * s, fun hm => ?_, by rwa [mul_smul]⟩
  rcases P.isPrime.mem_or_mem hm with h | h
  exacts [ht h, hs h]

theorem locP_AA (D : D7) (X : Fields) (s : Seam D X) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ)
    (cD : D.what₂.Tau → ℂ) (P : HeightOneSpectrum (𝓞 X.E)) (l : ℕ) (hl : l.Prime) (h2 : l ∉ D.host.small) (hq : l ≠ D.host.q)
    (hP : (l : 𝓞 X.E) ∈ P.asIdeal) (hc : Nat.Coprime (Ideal.absNorm cc) l) :
    localization₂ P.asIdeal (ambOf s B χ cD).AA = localization₂ P.asIdeal (1 : Submodule (𝓞 X.E) X.E) := by
  let j : 𝓞 D.host.E →+* 𝓞 X.E := RingOfIntegers.mapRingHom (s.iE.symm : D.host.E →+* X.E)
  have hj : ∀ a : 𝓞 D.host.E, ((j a : 𝓞 X.E) : X.E) = s.iE.symm (a : D.host.E) := fun _ => rfl
  haveI := P.isPrime
  refine le_antisymm (localization_le_of_le_localization₂ P ?_) (localization_le_of_le_localization₂ P ?_)
  · obtain ⟨z, hz, hden⟩ := exists_den D (P.asIdeal.comap j) hl h2 hq (by rw [Ideal.mem_comap, map_natCast]; exact hP)
    refine Submodule.span_le.2 ?_
    rintro r ⟨c, -, t, ht, rfl⟩
    obtain ⟨w, hw⟩ := hden t ht
    refine (mem_locP P _ _).2 ⟨j z, hz, Submodule.mem_one.2 ⟨j (algebraMap (𝓞 D.host.K) (𝓞 D.host.E) c * w), ?_⟩⟩
    rw [Algebra.smul_def]
    change ((j _ : 𝓞 X.E) : X.E) = ((j z : 𝓞 X.E) : X.E) * _
    rw [hj, hj, ← map_mul]
    congr 1
    have e : ((algebraMap (𝓞 D.host.K) (𝓞 D.host.E) c * w : 𝓞 D.host.E) : D.host.E) =
      ((c : D.host.K) : D.host.E) * (w : D.host.E) := rfl
    rw [e, hw]
    ring
  · intro x hx
    obtain ⟨y, rfl⟩ := Submodule.mem_one.1 hx
    refine (mem_locP P _ _).2 ⟨(Ideal.absNorm cc : ℕ), natCast_notMem P.isPrime.ne_top hP hc, ?_⟩
    have h1 : ((Ideal.absNorm cc : ℕ) : X.E) ∈ (ambOf s B χ cD).AA := by
      refine Submodule.subset_span ⟨_, Ideal.absNorm_mem cc, 1, Formalism.L2.Pj.one_mem_inverse_halfDifferent D, ?_⟩
      simp
    convert Submodule.smul_mem _ y h1 using 1
    simp [Algebra.smul_def, mul_comm]

theorem sq_ne_neg {X : Fields} (hX : X.Ok) (π : 𝓞 X.E) (p : ℕ) (hp : p.Prime) (hn : π * X.conjO π = (p : 𝓞 X.E))
    (hcop : IsCoprime π (X.conjO π)) (hcard : (divs π).card = X.f) (hN : ∀ P ∈ divs π, Ideal.absNorm P.asIdeal = p)
    (a : X.E) : a ^ 2 ≠ -(p : X.E) := by
  intro ha
  have hrk : Module.finrank ℚ X.E = 2 * X.f := by
    rw [← Module.finrank_mul_finrank ℚ X.F X.E, hX.rankE, Fields.f, hX.card_Tau, mul_comm]
  have hcc : ∀ x, X.conjO (X.conjO x) = x := fun x => RingOfIntegers.ext (star_star (x : X.E))
  obtain ⟨P, hP⟩ := Finset.card_pos.1 (hcard ▸ hX.f_pos)
  have hint : IsIntegral ℤ a := by
    refine IsIntegral.of_pow two_pos ?_
    rw [ha]
    exact (isIntegral_algebraMap (R := ℤ) (x := (p : ℤ)) |>.neg) |> fun h => by simpa using h
  obtain ⟨b, hba⟩ : ∃ b : 𝓞 X.E, algebraMap (𝓞 X.E) X.E b = a := ⟨⟨a, hint⟩, rfl⟩
  have hb : b ^ 2 = -(p : 𝓞 X.E) := by
    apply RingOfIntegers.coe_injective
    rw [map_pow, hba, ha, map_neg, map_natCast]
  have hpP : (p : 𝓞 X.E) ∈ P.asIdeal := hN P hP ▸ Ideal.absNorm_mem _
  have haP : b ∈ P.asIdeal :=
    P.isPrime.mem_of_pow_mem 2 (hb ▸ P.asIdeal.neg_mem hpP)
  refine GlobalTheory.SplitUnram.natCast_notMem_sq X.E X.conjO π p hcc hp hn hcop (by rw [hrk, hcard]) hN P hP ?_
  have := Ideal.pow_mem_pow haP 2
  rwa [hb, neg_mem_iff] at this

theorem notMem_small {X : Fields} (hX : X.Ok) (D : D7) (s : Seam D X) (π : 𝓞 X.E) (p : ℕ) (hp : p.Prime)
    (hn : π * X.conjO π = (p : 𝓞 X.E)) (hcop : IsCoprime π (X.conjO π)) (hcard : (divs π).card = X.f)
    (hN : ∀ P ∈ divs π, Ideal.absNorm P.asIdeal = p) : p ∉ D.host.small := by
  intro hs
  have hrk : Module.finrank ℚ X.E = 2 * X.f := by
    rw [← Module.finrank_mul_finrank ℚ X.F X.E, hX.rankE, Fields.f, hX.card_Tau, mul_comm]
  have hcc : ∀ x, X.conjO (X.conjO x) = x := fun x => RingOfIntegers.ext (star_star (x : X.E))
  obtain ⟨P, hP⟩ := Finset.card_pos.1 (hcard ▸ hX.f_pos)
  have hpP : (p : 𝓞 X.E) ∈ P.asIdeal := hN P hP ▸ Ideal.absNorm_mem _
  exact (UpperTheory.Ram.not_dvd_QS_of_notMem_sq D.host.toHostAx D.host.QS_exact X.E s.iE P p hp hpP
    (GlobalTheory.SplitUnram.natCast_notMem_sq X.E X.conjO π p hcc hp hn hcop (by rw [hrk, hcard]) hN P hP)).1
    (Nat.dvd_of_mem_primeFactors hs)

theorem primes_ne (Z : Dat) (D : D7) (s : Seam D Z.X) (hZ : Z.Ok) :
    (∀ u, Z.Pr.T u ∉ D.host.small ∧ Z.Pr.T u ≠ D.host.q) ∧ ∀ i, Z.Pr.g i ∉ D.host.small ∧ Z.Pr.g i ≠ D.host.q := by
  have ha : (s.iE.symm (D.host.sqq)) ^ 2 = -(D.host.q : Z.X.E) := by
    rw [← map_pow, D.host.sqq_sq, map_neg, map_natCast]
  have hcc : ∀ x, Z.X.conjO (Z.X.conjO x) = x := fun x => RingOfIntegers.ext (star_star (x : Z.X.E))
  have hPr := hZ.primes
  refine ⟨fun u => ⟨fun h => ?_, fun h => ?_⟩, fun i => ⟨fun h => ?_, fun h => ?_⟩⟩
  · exact notMem_small hZ.fields D s _ _ (hPr.T_prime u) (hPr.piT_norm u) (hPr.piT_cop u) (hPr.vT_card u) (hPr.vT_norm u) h
  · exact sq_ne_neg hZ.fields _ _ (hPr.T_prime u) (hPr.piT_norm u) (hPr.piT_cop u) (hPr.vT_card u) (hPr.vT_norm u) _ (h ▸ ha)
  · exact notMem_small hZ.fields D s (Z.X.conjO (Z.Pr.piG i)) _ (hPr.g_prime i) (by rw [hcc, mul_comm, hPr.piG_norm i])
      (by rw [hcc]; exact (hPr.piG_cop i).symm) (hPr.vG_card i) (hPr.vG_norm i) h
  · exact sq_ne_neg hZ.fields (Z.X.conjO (Z.Pr.piG i)) _ (hPr.g_prime i) (by rw [hcc, mul_comm, hPr.piG_norm i])
      (by rw [hcc]; exact (hPr.piG_cop i).symm) (hPr.vG_card i) (hPr.vG_norm i) _ (h ▸ ha)

theorem locP_AA_and_primes_ne : (∀ (D : D7) (X : Fields) (s : Seam D X) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ) (P : HeightOneSpectrum (𝓞 X.E)) (l : ℕ), l.Prime → l ∉ D.host.small → l ≠ D.host.q → (l : 𝓞 X.E) ∈ P.asIdeal → Nat.Coprime (Ideal.absNorm cc) l → localization₂ P.asIdeal (ambOf s B χ cD).AA = localization₂ P.asIdeal (1 : Submodule (𝓞 X.E) X.E)) ∧ ∀ (Z : Dat) (D : D7) (s : Seam D Z.X), Z.Ok → (∀ u, Z.Pr.T u ∉ D.host.small ∧ Z.Pr.T u ≠ D.host.q) ∧ ∀ i, Z.Pr.g i ∉ D.host.small ∧ Z.Pr.g i ≠ D.host.q :=
  ⟨locP_AA, primes_ne⟩

end GlobalTheory.AAUnitAway
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.L2.Th1.H GlobalTheory.IndefiniteRowSideFullHecke.JetSumTable GlobalTheory.MomT

namespace GlobalTheory.RepsMod

variable {H : Type} [AddCommGroup H]

theorem sum_eq_of_family {M ι : Type} [AddCommMonoid M] {Λ B : AddSubgroup H} {R : Finset H}
    (hR : IsReps Λ B R) (s : Finset ι) (f : ι → H) (hf : ∀ i ∈ s, f i ∈ B)
    (hinj : ∀ i ∈ s, ∀ j ∈ s, f i - f j ∈ Λ → i = j) (hsurj : ∀ y ∈ B, ∃ i ∈ s, y - f i ∈ Λ)
    (F : H → M) (hF : ∀ y ∈ B, ∀ l ∈ Λ, l ∈ B → F (y + l) = F y) :
    ∑ y ∈ R, F y = ∑ i ∈ s, F (f i) := by
  obtain ⟨h1, h2, h3⟩ := hR
  symm
  choose r hr hrl using fun i (hi : i ∈ s) => h3 (f i) (hf i hi)
  refine Finset.sum_bij r hr ?_ ?_ ?_
  · intro i hi j hj hij
    apply hinj i hi j hj
    have := Λ.sub_mem (hrl i hi) (hrl j hj)
    rw [hij] at this
    simpa using this
  · intro y hy
    obtain ⟨i, hi, hl⟩ := hsurj y (h1 y hy)
    refine ⟨i, hi, ?_⟩
    symm
    apply h2 y hy _ (hr i hi)
    have := Λ.add_mem hl (hrl i hi)
    simpa using this
  · intro i hi
    have := hF (r i hi) (h1 _ (hr i hi)) _ (hrl i hi) (B.sub_mem (hf i hi) (h1 _ (hr i hi)))
    simpa using this

theorem out_sub_mem_iff (Λ B : AddSubgroup H) (x y : B) :
    ((x : H) - y ∈ Λ) ↔ (QuotientAddGroup.mk x : B ⧸ Λ.addSubgroupOf B) = QuotientAddGroup.mk y := by
  rw [QuotientAddGroup.eq_iff_sub_mem, AddSubgroup.mem_addSubgroupOf]
  simp

theorem out_inj (Λ B : AddSubgroup H) (c d : B ⧸ Λ.addSubgroupOf B)
    (h : ((c.out : B) : H) - (d.out : B) ∈ Λ) : c = d := by
  rw [out_sub_mem_iff] at h
  simpa using h

theorem out_surj (Λ B : AddSubgroup H) (y : H) (hy : y ∈ B) :
    ∃ c : B ⧸ Λ.addSubgroupOf B, y - ((c.out : B) : H) ∈ Λ := by
  refine ⟨QuotientAddGroup.mk ⟨y, hy⟩, ?_⟩
  have := (out_sub_mem_iff Λ B ⟨y, hy⟩ (Quotient.out (QuotientAddGroup.mk ⟨y, hy⟩ : B ⧸ Λ.addSubgroupOf B))).2 (by simp)
  exact this

theorem exists_reps (Λ B : AddSubgroup H) (h : Λ.relIndex B ≠ 0) : ∃ R : Finset H, IsReps Λ B R := by
  classical
  have : Finite (B ⧸ Λ.addSubgroupOf B) := Nat.finite_of_card_ne_zero h
  have := Fintype.ofFinite (B ⧸ Λ.addSubgroupOf B)
  refine ⟨Finset.univ.image (fun c : B ⧸ Λ.addSubgroupOf B => ((c.out : B) : H)), ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨c, -, rfl⟩ := Finset.mem_image.1 hx
    exact (c.out).2
  · intro x hx y hy hxy
    obtain ⟨c, -, rfl⟩ := Finset.mem_image.1 hx
    obtain ⟨d, -, rfl⟩ := Finset.mem_image.1 hy
    rw [out_inj Λ B c d hxy]
  · intro y hy
    obtain ⟨c, hc⟩ := out_surj Λ B y hy
    exact ⟨_, Finset.mem_image.2 ⟨c, Finset.mem_univ _, rfl⟩, hc⟩

theorem card_reps (Λ B : AddSubgroup H) (R : Finset H) (hR : IsReps Λ B R) :
    R.card = Λ.relIndex B := by
  classical
  have : Finite (B ⧸ Λ.addSubgroupOf B) := by
    refine Finite.of_surjective (fun x : R => (QuotientAddGroup.mk ⟨x.1, hR.1 _ x.2⟩ : B ⧸ Λ.addSubgroupOf B)) ?_
    intro c
    obtain ⟨x, hx, hl⟩ := hR.2.2 _ (c.out).2
    refine ⟨⟨x, hx⟩, ?_⟩
    have := (out_sub_mem_iff Λ B c.out ⟨x, hR.1 _ hx⟩).1 hl
    simpa using this.symm
  have := Fintype.ofFinite (B ⧸ Λ.addSubgroupOf B)
  have h := sum_eq_of_family hR Finset.univ (fun c : B ⧸ Λ.addSubgroupOf B => ((c.out : B) : H))
    (fun c _ => (c.out).2) (fun c _ d _ h => out_inj Λ B c d h)
    (fun y hy => by
      obtain ⟨c, hc⟩ := out_surj Λ B y hy
      exact ⟨c, Finset.mem_univ _, hc⟩) (fun _ => (1 : ℕ)) (fun _ _ _ _ _ => rfl)
  simp only [Finset.sum_const, smul_eq_mul, mul_one, Finset.card_univ] at h
  rw [h, ← Nat.card_eq_fintype_card]
  rfl

theorem sum_prod_reps (M : Type) [AddCommMonoid M] (Λ B B₁ B₂ : AddSubgroup H) (R R₁ R₂ : Finset H)
    (F : H → M) (h1 : B₁ ≤ B) (h2 : B₂ ≤ B) (hs : ∀ y ∈ B, ∃ y₁ ∈ B₁, ∃ y₂ ∈ B₂, y - (y₁ + y₂) ∈ Λ)
    (hi : ∀ y₁ ∈ B₁, ∀ y₂ ∈ B₂, y₁ + y₂ ∈ Λ → y₁ ∈ Λ) (hR : IsReps Λ B R) (hR₁ : IsReps Λ B₁ R₁)
    (hR₂ : IsReps Λ B₂ R₂) (hF : ∀ y ∈ B, ∀ l ∈ Λ, l ∈ B → F (y + l) = F y) :
    ∑ y ∈ R, F y = ∑ y₂ ∈ R₂, ∑ y₁ ∈ R₁, F (y₁ + y₂) := by
  rw [← Finset.sum_product']
  refine sum_eq_of_family hR (R₂ ×ˢ R₁) (fun p => p.2 + p.1) ?_ ?_ ?_ F hF
  · intro p hp
    rw [Finset.mem_product] at hp
    exact B.add_mem (h1 (hR₁.1 _ hp.2)) (h2 (hR₂.1 _ hp.1))
  · intro p hp q hq hpq
    rw [Finset.mem_product] at hp hq
    have e : p.2 + p.1 - (q.2 + q.1) = (p.2 - q.2) + (p.1 - q.1) := by abel
    simp only [e] at hpq
    have a1 := hi _ (B₁.sub_mem (hR₁.1 _ hp.2) (hR₁.1 _ hq.2)) _
      (B₂.sub_mem (hR₂.1 _ hp.1) (hR₂.1 _ hq.1)) hpq
    have a2 : p.1 - q.1 ∈ Λ := by
      have := Λ.sub_mem hpq a1
      simpa using this
    exact Prod.ext (hR₂.2.1 _ hp.1 _ hq.1 a2) (hR₁.2.1 _ hp.2 _ hq.2 a1)
  · intro y hy
    obtain ⟨y₁, hy₁, y₂, hy₂, hl⟩ := hs y hy
    obtain ⟨r₁, hr₁, hl₁⟩ := hR₁.2.2 _ hy₁
    obtain ⟨r₂, hr₂, hl₂⟩ := hR₂.2.2 _ hy₂
    refine ⟨(r₂, r₁), Finset.mem_product.2 ⟨hr₂, hr₁⟩, ?_⟩
    have e : y - (r₁ + r₂) = (y - (y₁ + y₂)) + (y₁ - r₁) + (y₂ - r₂) := by abel
    simp only [e]
    exact Λ.add_mem (Λ.add_mem hl hl₁) hl₂

theorem sum_char_reps (K : Type) [Field K] (Λ B : AddSubgroup H) (R : Finset H) (φ : H → K)
    (hR : IsReps Λ B R) (hm : ∀ x ∈ B, ∀ y ∈ B, φ (x + y) = φ x * φ y)
    (h1 : ∀ x ∈ B, x ∈ Λ → φ x = 1) :
    ((∀ y ∈ B, φ y = 1) → ∑ y ∈ R, φ y = (R.card : K)) ∧
      ((¬ ∀ y ∈ B, φ y = 1) → ∑ y ∈ R, φ y = 0) := by
  constructor
  · intro h
    rw [Finset.sum_congr rfl (fun y hy => h y (hR.1 y hy))]
    simp
  · intro h
    push Not at h
    obtain ⟨y₀, hy₀, hne⟩ := h
    have key := sum_eq_of_family hR R (fun y => y₀ + y) (fun y hy => B.add_mem hy₀ (hR.1 y hy))
      (fun x hx y hy hxy => hR.2.1 x hx y hy (by simpa using hxy))
      (fun y hy => by
        obtain ⟨x, hx, hl⟩ := hR.2.2 _ (B.sub_mem hy hy₀)
        exact ⟨x, hx, by rwa [← sub_sub]⟩) φ
      (fun y hy l hl hlB => by rw [hm y hy l hlB, h1 l hlB hl, mul_one])
    rw [Finset.sum_congr rfl (fun y hy => hm y₀ hy₀ y (hR.1 y hy)), ← Finset.mul_sum] at key
    have : (φ y₀ - 1) * ∑ y ∈ R, φ y = 0 := by rw [_root_.sub_mul, one_mul, ← key, sub_self]
    exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hne)

theorem not_dvd_relIndex (Λ B : AddSubgroup H) (g p : ℕ) (hp : p.Prime) (hc : Nat.Coprime g p)
    (h : Λ.relIndex B ≠ 0) (hg : ∀ x ∈ B, g • x ∈ Λ) : ¬ p ∣ Λ.relIndex B := by
  intro hd
  have : Finite (B ⧸ Λ.addSubgroupOf B) := Nat.finite_of_card_ne_zero h
  have := Fact.mk hp
  obtain ⟨c, hcc⟩ := exists_prime_addOrderOf_dvd_card' (G := B ⧸ Λ.addSubgroupOf B) p hd
  have h0 : g • c = 0 := by
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective c
    rw [← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf]
    simpa using hg x x.2
  have hdg : p ∣ g := hcc ▸ addOrderOf_dvd_of_nsmul_eq_zero h0
  exact (hp.coprime_iff_not_dvd.1 hc.symm) hdg

theorem reps_facts : ∀ (H : Type) [AddCommGroup H], (∀ Λ B : AddSubgroup H, Λ.relIndex B ≠ 0 → ∃ R : Finset H, IsReps Λ B R) ∧ (∀ (Λ B : AddSubgroup H) (R : Finset H), IsReps Λ B R → R.card = Λ.relIndex B) ∧ (∀ (M : Type) [AddCommMonoid M] (Λ B B₁ B₂ : AddSubgroup H) (R R₁ R₂ : Finset H) (F : H → M), B₁ ≤ B → B₂ ≤ B → (∀ y ∈ B, ∃ y₁ ∈ B₁, ∃ y₂ ∈ B₂, y - (y₁ + y₂) ∈ Λ) → (∀ y₁ ∈ B₁, ∀ y₂ ∈ B₂, y₁ + y₂ ∈ Λ → y₁ ∈ Λ) → IsReps Λ B R → IsReps Λ B₁ R₁ → IsReps Λ B₂ R₂ → (∀ y ∈ B, ∀ l ∈ Λ, l ∈ B → F (y + l) = F y) → ∑ y ∈ R, F y = ∑ y₂ ∈ R₂, ∑ y₁ ∈ R₁, F (y₁ + y₂)) ∧ (∀ (K : Type) [Field K] (Λ B : AddSubgroup H) (R : Finset H) (φ : H → K), IsReps Λ B R → (∀ x ∈ B, ∀ y ∈ B, φ (x + y) = φ x * φ y) → (∀ x ∈ B, x ∈ Λ → φ x = 1) → ((∀ y ∈ B, φ y = 1) → ∑ y ∈ R, φ y = (R.card : K)) ∧ ((¬ ∀ y ∈ B, φ y = 1) → ∑ y ∈ R, φ y = 0)) ∧ ∀ (Λ B : AddSubgroup H) (g p : ℕ), p.Prime → Nat.Coprime g p → Λ.relIndex B ≠ 0 → (∀ x ∈ B, g • x ∈ Λ) → ¬ p ∣ Λ.relIndex B :=
  fun _ _ => ⟨exists_reps, card_reps, sum_prod_reps, sum_char_reps, not_dvd_relIndex⟩

end GlobalTheory.RepsMod
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.L2.Th1.H GlobalTheory.IndefiniteRowSideFullHecke.JetSumTable GlobalTheory.MomT

namespace GlobalTheory.MomT.DualCount

theorem relIndex_le_of_selfDual (H : Type) [AddCommGroup H] (ω : H → H → ℝ)
    (Λ₁ Λ₂ : AddSubgroup H) (hadd : ∀ x y z, ω (x + y) z = ω x z + ω y z)
    (hanti : ∀ x y, ω x y = -ω y x)
    (h₁ : ∀ x, x ∈ Λ₁ ↔ ∀ y ∈ Λ₁, ∃ n : ℤ, ω x y = n)
    (h₂ : ∀ x, x ∈ Λ₂ ↔ ∀ y ∈ Λ₂, ∃ n : ℤ, ω x y = n)
    (hfin : Λ₁.relIndex Λ₂ ≠ 0) : Λ₂.relIndex Λ₁ ≤ Λ₁.relIndex Λ₂ := by
  classical
  have hadd' : ∀ x y z, ω x (y + z) = ω x y + ω x z := by
    intro x y z
    rw [hanti x (y + z), hadd, hanti x y, hanti x z]; ring
  have hsub : ∀ x y z, ω (x - y) z = ω x z - ω y z := by
    intro x y z
    have := hadd (x - y) y z
    rw [sub_add_cancel] at this
    linarith
  have hint : ∀ r : ℝ, ((r : ℝ) : UnitAddCircle) = 0 ↔ ∃ n : ℤ, r = n := by
    intro r
    rw [AddCircle.coe_eq_zero_iff]
    constructor
    · rintro ⟨n, hn⟩; exact ⟨n, by simpa using hn.symm⟩
    · rintro ⟨n, hn⟩; exact ⟨n, by simpa using hn.symm⟩
  let φ : H → (Λ₂ →+ UnitAddCircle) := fun x =>
    AddMonoidHom.mk' (fun y => ((ω x y : ℝ) : UnitAddCircle)) (by
      intro a b
      simp only [AddSubgroup.coe_add, hadd', AddCircle.coe_add])
  have hφ : ∀ x : Λ₁, Λ₁.addSubgroupOf Λ₂ ≤ (φ x).ker := by
    intro x y hy
    rw [AddMonoidHom.mem_ker]
    exact (hint _).2 ((h₁ x).1 x.2 y (AddSubgroup.mem_addSubgroupOf.1 hy))
  let ψ : Λ₁ → (Λ₂ ⧸ Λ₁.addSubgroupOf Λ₂ →+ UnitAddCircle) := fun x =>
    QuotientAddGroup.lift _ (φ x) (hφ x)
  haveI : Fact ((0 : ℝ) < 1) := ⟨one_pos⟩
  let χ : Λ₁ → AddChar (Λ₂ ⧸ Λ₁.addSubgroupOf Λ₂) Circle := fun x =>
    (AddCircle.toCircle_addChar (T := 1)).compAddMonoidHom (ψ x)
  have hχ : ∀ a b : Λ₁, χ a = χ b → ((a : H) - b) ∈ Λ₂ := by
    intro a b hab
    rw [h₂]
    intro y hy
    have h := DFunLike.congr_fun hab (QuotientAddGroup.mk ⟨y, hy⟩)
    have h' : AddCircle.toCircle (((ω a y : ℝ)) : UnitAddCircle)
        = AddCircle.toCircle (((ω b y : ℝ)) : UnitAddCircle) := h
    have h'' := AddCircle.injective_toCircle (T := 1) one_ne_zero h'
    rw [← hint, hsub, AddCircle.coe_sub, h'', sub_self]
  haveI hG : Finite (Λ₂ ⧸ Λ₁.addSubgroupOf Λ₂) := Nat.finite_of_card_ne_zero hfin
  haveI : Fintype (Λ₂ ⧸ Λ₁.addSubgroupOf Λ₂) := Fintype.ofFinite _
  let f : (Λ₁ ⧸ Λ₂.addSubgroupOf Λ₁) → AddChar (Λ₂ ⧸ Λ₁.addSubgroupOf Λ₂) ℂ := fun q =>
    AddChar.circleEquivComplex (χ q.out)
  have hf : Function.Injective f := by
    intro p q hpq
    have h := hχ _ _ (AddChar.circleEquivComplex.injective hpq)
    rw [← QuotientAddGroup.out_eq' p, ← QuotientAddGroup.out_eq' q, QuotientAddGroup.eq_iff_sub_mem,
      AddSubgroup.mem_addSubgroupOf]
    exact h
  have hle := Nat.card_le_card_of_injective f hf
  have hc : Nat.card (AddChar (Λ₂ ⧸ Λ₁.addSubgroupOf Λ₂) ℂ)
      = Nat.card (Λ₂ ⧸ Λ₁.addSubgroupOf Λ₂) := by
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, AddChar.card_eq]
  rw [hc] at hle
  exact hle

theorem relIndex_eq_of_selfDual : ∀ (H : Type) [AddCommGroup H] (ω : H → H → ℝ)
    (Λ₁ Λ₂ : AddSubgroup H), (∀ x y z, ω (x + y) z = ω x z + ω y z) → (∀ x y, ω x y = -ω y x) →
    (∀ x, x ∈ Λ₁ ↔ ∀ y ∈ Λ₁, ∃ n : ℤ, ω x y = n) → (∀ x, x ∈ Λ₂ ↔ ∀ y ∈ Λ₂, ∃ n : ℤ, ω x y = n) →
    Λ₁.relIndex Λ₂ ≠ 0 → Λ₂.relIndex Λ₁ ≠ 0 → Λ₁.relIndex Λ₂ = Λ₂.relIndex Λ₁ := by
  intro H _ ω Λ₁ Λ₂ hadd hanti h₁ h₂ f₁ f₂
  exact le_antisymm (relIndex_le_of_selfDual H ω Λ₂ Λ₁ hadd hanti h₂ h₁ f₂)
    (relIndex_le_of_selfDual H ω Λ₁ Λ₂ hadd hanti h₁ h₂ f₁)

end GlobalTheory.MomT.DualCount
end
