module

public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle031
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle038
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle043
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle044
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle052
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle051
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle567
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSimpleRingOfCentralIdem
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle019
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle018
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.CechModulesFunctorShortExactOfAcyclic
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.HigherDirectImagesVanishOfIsAffineHom
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open CategoryTheory Limits AlgebraicGeometry

noncomputable section

namespace GlobalTheory.EtC.Tr

variable (R : Type) [CommRing R]

theorem splits_of_splitSieve {Z X S V : Scheme.{0}} {f : Z ⟶ X} {x : S ⟶ X} {v : V ⟶ S} (hv : splitSieve f x v) :
    Splits f (v ≫ x) := by
  obtain ⟨W, w, u, ⟨m, s, hs⟩, rfl⟩ := hv
  refine ⟨m, fun j => w ≫ s j, ?_⟩
  have := GlobalTheory.T.splitBy_baseChange' hs w
  rwa [Category.assoc]

def splitSum {Z X V : Scheme.{0}} (f : Z ⟶ X) (y : V ⟶ X) (h : Splits f y) : freeSch R V ⟶ freeSch R Z :=
  ∑ j, (free R).map (yoneda.map (h.choose_spec.choose j))

theorem splitSum_eq {Z X V : Scheme.{0}} {f : Z ⟶ X} {y : V ⟶ X} (h : Splits f y) {m : ℕ} {s : Fin m → (V ⟶ Z)}
    (hs : SplitBy f y s) : splitSum R f y h = ∑ j, (free R).map (yoneda.map (s j)) :=
  GlobalTheory.T.freeSheaf_sum_sections_eq_of_two_splittings R h.choose_spec.choose_spec hs

theorem existsUnique_isTransfer {Z X : Scheme.{0}} (f : Z ⟶ X) [IsFinite f] [Etale f] :
    ∃! t, IsTransfer R f t := by
  have hT := GlobalTheory.T.splittingSieve_mem_etaleTopology f (𝟙 X)

  let σ : ∀ ⦃V : Scheme.{0}⦄ (v : V ⟶ X), splitSieve f (𝟙 X) v → (freeSch R V ⟶ freeSch R Z) :=
    fun V v hv => splitSum R f (v ≫ 𝟙 X) (splits_of_splitSieve hv)
  have hσ : ∀ ⦃V W : Scheme.{0}⦄ (v : V ⟶ X) (hv : splitSieve f (𝟙 X) v) (g : W ⟶ V),
      (free R).map (yoneda.map g) ≫ σ v hv = σ (g ≫ v) ((splitSieve f (𝟙 X)).downward_closed hv g) := by
    intro V W v hv g
    obtain ⟨m, s, hs⟩ := splits_of_splitSieve hv
    have hg := GlobalTheory.T.splitBy_baseChange' hs g
    rw [← Category.assoc] at hg
    simp only [σ, splitSum_eq R _ hs, splitSum_eq R _ hg, Preadditive.comp_sum, ← Functor.map_comp]
  obtain ⟨t, ht⟩ := GlobalTheory.T.exists_freeSch_hom_glue_of_etale_covering R (freeSch R Z) _ hT σ hσ
  have key : ∀ t', IsTransfer R f t' → ∀ ⦃V : Scheme.{0}⦄ (v : V ⟶ X) (hv : splitSieve f (𝟙 X) v),
      (free R).map (yoneda.map v) ≫ t' = σ v hv := by
    intro t' ht' V v hv
    obtain ⟨m, s, hs⟩ := splits_of_splitSieve hv
    simp only [σ, splitSum_eq R _ hs]
    have := ht'.apply_of_splitBy R hs
    rwa [Category.comp_id] at this
  refine ⟨t, ?_, fun t' ht' => ?_⟩
  · intro S x m s hs hiso
    refine GlobalTheory.T.freeSch_hom_ext_of_etale_covering R (freeSch R Z) _ _ _ (GlobalTheory.T.splittingSieve_mem_etaleTopology f x) (fun V v hv => ?_)
    obtain ⟨m', s', hs'⟩ := splits_of_splitSieve hv
    have hvx : splitSieve f (𝟙 X) (v ≫ x) := ⟨V, 𝟙 V, v ≫ x, (show Splits f ((v ≫ x) ≫ 𝟙 X) by rw [Category.comp_id]; exact ⟨m', s', hs'⟩), Category.id_comp _⟩
    have h1 := GlobalTheory.T.splitBy_baseChange' ⟨hs, hiso⟩ v
    rw [← Category.assoc, ← Functor.map_comp, ← Functor.map_comp, ht _ hvx, Preadditive.comp_sum]
    simp only [σ, ← Functor.map_comp]
    rw [splitSum_eq R _ (show SplitBy f ((v ≫ x) ≫ 𝟙 X) (fun j => v ≫ s j) by rw [Category.comp_id]; exact h1)]
  · exact GlobalTheory.T.freeSch_hom_ext_of_etale_covering R (freeSch R Z) _ _ _ hT fun V v hv => by rw [key t' ht' v hv, ht v hv]

end GlobalTheory.EtC.Tr

end
end

section

open GlobalTheory.Pst.StLat

namespace GlobalTheory.Pst.StLat

theorem clos_eq_zero_of_mul_mem {R : Type} [CommRing R] [IsDomain R] (p : ℕ) (hp : p.Prime)
    (hpu : IsUnit ((p : ℕ) : R)) (π : R) (hπ : π ≠ 0)
    (hsep : ∀ x : R, (∀ n : ℕ, π ^ n ∣ x) → x = 0) (S : Subring R)
    (hdiv : ∀ s ∈ S, ∀ i : ℕ, π ^ i ∣ s → ∃ s' ∈ S, s = π ^ i * s')
    (hres : ∀ y : R, (∀ k : ℕ, ∃ s ∈ S, π ∣ y - ((p : ℕ) : R) ^ k * s) → π ∣ y)
    (u : R) (hlog : ∀ m : ℕ, 1 ≤ m → ∃ s ∈ S, ∃ e : R, (e = 1 ∨ e = -1) ∧
      π ^ (2 * p ^ m) ∣ ((p : ℕ) : R) * (((p : ℕ) : R) ^ (m - 1) * u - s) - e * π ^ (p ^ m))
    (a : R) (r : ℕ) (ha : a ∈ Clos S π) (hau : ((p : ℕ) : R) ^ r * a * u ∈ Clos S π) : a = 0 := by
  obtain ⟨q, hPq⟩ : ∃ q : R, ((p : ℕ) : R) * q = 1 := ⟨((hpu.unit⁻¹ : Rˣ) : R), hpu.mul_val_inv⟩
  have hSC : ∀ s ∈ S, s ∈ Clos S π := fun s hs n => ⟨s, hs, by simp⟩
  have hPC : ((p : ℕ) : R) ∈ Clos S π := natCast_mem _ _

  have stepD : ∀ b ∈ Clos S π, ∀ r' : ℕ, ((p : ℕ) : R) ^ r' * b * u ∈ Clos S π →
      ∃ b' ∈ Clos S π, ((p : ℕ) : R) * b' = b := by
    intro b hb r' hbu
    refine ⟨q * b, ?_, by rw [← mul_assoc, hPq, one_mul]⟩
    intro n
    obtain ⟨s, hs, e, he, w, hw⟩ := hlog (r' + n + 1) (by omega)
    have hm : r' + n + 1 - 1 = r' + n := by omega
    rw [hm] at hw
    set M := p ^ (r' + n + 1) with hMdef
    have hnM : n ≤ M := by
      have h1 : r' + n + 1 < p ^ (r' + n + 1) := Nat.lt_pow_self hp.one_lt
      omega
    have h2M : π ^ (2 * M) = π ^ M * π ^ M := by rw [two_mul, pow_add]
    rw [h2M] at hw
    have hx : b * (((p : ℕ) : R) ^ (r' + n) * u - s) ∈ Clos S π := by
      have : b * (((p : ℕ) : R) ^ (r' + n) * u - s) =
          ((p : ℕ) : R) ^ n * (((p : ℕ) : R) ^ r' * b * u) - b * s := by ring
      rw [this]
      exact sub_mem (mul_mem (pow_mem hPC _) hbu) (mul_mem hb (hSC s hs))
    obtain ⟨s₁, hs₁, c, hc⟩ := hx (2 * M)
    rw [h2M] at hc
    have hs1eq : s₁ = π ^ M * (q * b * e + π ^ M * (q * b * w - c)) := by
      linear_combination (-1 : R) * hc + (q * b) * hw - (b * (((p : ℕ) : R) ^ (r' + n) * u - s)) * hPq
    obtain ⟨s₂, hs₂S, hs₂⟩ := hdiv s₁ hs₁ M ⟨_, hs1eq⟩
    have hcan : q * b * e - s₂ = π ^ M * (c - q * b * w) := by
      apply mul_left_cancel₀ (pow_ne_zero M hπ)
      linear_combination hs₂ - hs1eq
    have he2 : e * e = 1 := by rcases he with rfl | rfl <;> ring
    have heS : e * s₂ ∈ S := by
      rcases he with rfl | rfl
      · simpa using hs₂S
      · simpa using neg_mem hs₂S
    refine ⟨e * s₂, heS, dvd_trans (pow_dvd_pow π hnM) ⟨e * (c - q * b * w), ?_⟩⟩
    linear_combination e * hcan - (q * b) * he2

  have iter : ∀ k : ℕ, ∃ b ∈ Clos S π, ((p : ℕ) : R) ^ k * b = a ∧
      ((p : ℕ) : R) ^ (r + k) * b * u ∈ Clos S π := by
    intro k
    induction k with
    | zero => exact ⟨a, ha, by simp, by simpa using hau⟩
    | succ k ih =>
      obtain ⟨b, hb, hbk, hbu⟩ := ih
      obtain ⟨b', hb', hPb'⟩ := stepD b hb (r + k) hbu
      refine ⟨b', hb', ?_, ?_⟩
      · rw [pow_succ, mul_assoc, hPb', hbk]
      · have : ((p : ℕ) : R) ^ (r + (k + 1)) * b' * u =
            ((p : ℕ) : R) ^ (r + k) * (((p : ℕ) : R) * b') * u := by ring
        rw [this, hPb']
        exact hbu

  by_contra ha0
  classical
  have hex : ∃ n : ℕ, ¬ π ^ n ∣ a := by
    by_contra h
    push_neg at h
    exact ha0 (hsep a h)
  have hn0 : Nat.find hex ≠ 0 := by
    intro h0
    have := Nat.find_spec hex
    rw [h0, pow_zero] at this
    exact this (one_dvd a)
  set i := Nat.find hex - 1 with hidef
  have hi1 : i + 1 = Nat.find hex := by omega
  have hia : π ^ i ∣ a := by
    have := Nat.find_min hex (show i < Nat.find hex by omega)
    simpa using this
  obtain ⟨a₁, ha₁⟩ := hia
  have hna₁ : ¬ π ∣ a₁ := by
    rintro ⟨t, ht⟩
    apply Nat.find_spec hex
    rw [← hi1]
    exact ⟨t, by rw [ha₁, ht, pow_succ]; ring⟩
  apply hna₁
  apply hres a₁
  intro k
  obtain ⟨b, hb, hbk, -⟩ := iter k
  obtain ⟨s, hs, hbs⟩ := hb (i + 1)
  have hib : π ^ i ∣ b := ⟨q ^ k * a₁, by
    have : b = q ^ k * (((p : ℕ) : R) ^ k * b) := by
      rw [← mul_assoc, ← mul_pow, mul_comm q, hPq, one_pow, one_mul]
    rw [this, hbk, ha₁]; ring⟩
  have his : π ^ i ∣ s := by
    have h1 : π ^ i ∣ b - s := dvd_trans (pow_dvd_pow π (Nat.le_succ i)) hbs
    have := dvd_sub hib h1
    simpa using this
  obtain ⟨s', hs'S, hs'⟩ := hdiv s hs i his
  refine ⟨s', hs'S, ?_⟩
  rw [← mul_dvd_mul_iff_left (pow_ne_zero i hπ), ← pow_succ]
  have : π ^ i * (a₁ - ((p : ℕ) : R) ^ k * s') = ((p : ℕ) : R) ^ k * (b - s) := by
    rw [mul_sub, ← ha₁, ← hbk, hs']; ring
  rw [this]
  exact dvd_mul_of_dvd_right hbs _

end GlobalTheory.Pst.StLat
end

section

namespace GlobalTheory.UPel.HT.Gen.SplitAE
open NumberField GlobalTheory.LKInvGood
open scoped TensorProduct

theorem finrank_eq (G : GDatum) : Module.finrank G.F (ℚ ⊗[ℤ] G.O) = G.m ^ 2 := by
  haveI := G.freeO
  haveI := G.finO
  have h1 : Module.finrank ℚ (ℚ ⊗[ℤ] G.O) = Module.finrank ℤ G.O := Module.finrank_baseChange
  haveI : Module.Finite ℚ (ℚ ⊗[ℤ] G.O) := inferInstance
  haveI : Module.Finite G.F (ℚ ⊗[ℤ] G.O) := Module.Finite.of_restrictScalars_finite ℚ G.F _
  have h2 := Module.finrank_mul_finrank ℚ G.F (ℚ ⊗[ℤ] G.O)
  rw [h1, G.rankO] at h2
  have hd : 0 < Module.finrank ℚ G.F := Module.finrank_pos
  have : Module.finrank ℚ G.F * Module.finrank G.F (ℚ ⊗[ℤ] G.O) = Module.finrank ℚ G.F * G.m ^ 2 := by
    rw [h2, mul_comm]
  exact Nat.eq_of_mul_eq_mul_left hd this

theorem isCentral (G : GDatum) : Algebra.IsCentral G.F (ℚ ⊗[ℤ] G.O) := by
  refine ⟨fun z hz => ?_⟩
  rw [Subalgebra.mem_center_iff] at hz
  obtain ⟨N, hN, x, hx⟩ := GDatum.exists_smul_eq_tmul G z
  have hxc : ∀ y : G.O, x * y = y * x := by
    intro y
    apply GDatum.tmul_one_injective G
    have e1 : (1:ℚ) ⊗ₜ[ℤ] (x*y) = N • (z * (1 ⊗ₜ y)) := by
      rw [← smul_mul_assoc, hx, Algebra.TensorProduct.tmul_mul_tmul, mul_one]
    have e2 : (1:ℚ) ⊗ₜ[ℤ] (y*x) = N • ((1 ⊗ₜ y) * z) := by
      rw [← mul_smul_comm, hx, Algebra.TensorProduct.tmul_mul_tmul, mul_one]
    show (1:ℚ) ⊗ₜ[ℤ] (x*y) = (1:ℚ) ⊗ₜ[ℤ] (y*x)
    rw [e1, e2, hz]
  obtain ⟨c, e, he, hec⟩ := G.central x hxc
  have hM : ((e * N : ℤ) : ℚ) • z = algebraMap G.F (ℚ ⊗[ℤ] G.O) (c : G.F) := by
    rw [algebraMap_F_coe, ← hec, Int.cast_smul_eq_zsmul, mul_smul, hx, TensorProduct.tmul_smul]
  have hq : ((e * N : ℤ) : ℚ) ≠ 0 := by exact_mod_cast mul_ne_zero he hN
  refine ⟨((e * N : ℤ) : ℚ)⁻¹ • (c : G.F), ?_⟩
  show algebraMap G.F (ℚ ⊗[ℤ] G.O) (((e * N : ℤ) : ℚ)⁻¹ • (c : G.F)) = z
  rw [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply, ← Algebra.smul_def, ← hM, smul_smul, inv_mul_cancel₀ hq, one_smul]

theorem ordB_finite (G : GDatum) : Module.Finite ℤ (ordB G) := by
  haveI := G.finO
  let f := (Algebra.TensorProduct.includeRight (R := ℤ) (A := ℚ) (B := G.O)).toRingHom
  exact Module.Finite.of_surjective f.rangeRestrict.toIntAlgHom.toLinearMap f.rangeRestrict_surjective

theorem ordB_denom (G : GDatum) (b : ℚ ⊗[ℤ] G.O) : ∃ n : ℕ, 0 < n ∧ (n : ℚ ⊗[ℤ] G.O) * b ∈ ordB G := by
  obtain ⟨N, hN, x, hx⟩ := GDatum.exists_smul_eq_tmul G b
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg N
  · refine ⟨n, by omega, x, ?_⟩
    show (1 : ℚ) ⊗ₜ[ℤ] x = _
    rw [← hx, natCast_zsmul, nsmul_eq_mul]
  · refine ⟨n, by omega, -x, ?_⟩
    show (1 : ℚ) ⊗ₜ[ℤ] (-x) = _
    rw [TensorProduct.tmul_neg, ← hx, neg_smul, neg_neg, natCast_zsmul, nsmul_eq_mul]

theorem splitAE : ∀ (G : GDatum), ∃ M : ℕ, 0 < M ∧ ∀ (p : ℕ) [Fact p.Prime], ¬ p ∣ M →
    Nonempty ((G.O ⊗[ℤ] ℤ_[p]) ≃ₐ[𝓞 G.F] Matrix (Fin G.m) (Fin G.m) (𝓞 G.F ⊗[ℤ] ℤ_[p])) := by
  intro G
  haveI := G.freeO
  haveI := G.finO
  haveI := isCentral G
  haveI := GDatum.isSimpleRing G
  haveI : FiniteDimensional G.F (ℚ ⊗[ℤ] G.O) := Module.Finite.of_restrictScalars_finite ℚ G.F _
  obtain ⟨N, hN, hloc⟩ := GlobalTheory.T.adjoinLocalOrderTensorPadic_matrix_almost_all G.F (ℚ ⊗[ℤ] G.O) G.m (finrank_eq G) (ordB G) (ordB_finite G) (ordB_denom G)
  refine ⟨N, hN, fun p _ hp => ?_⟩
  obtain ⟨ψ, hψ⟩ := hloc p hp
  obtain ⟨ι, hι⟩ : ∃ ι : G.O ⊗[ℤ] ℤ_[p] ≃+* locOrder p (ordB G),
      ∀ o : G.O, (ι (o ⊗ₜ[ℤ] 1) : ℚ_[p] ⊗[ℚ] (ℚ ⊗[ℤ] G.O)) = (1 : ℚ_[p]) ⊗ₜ[ℚ] ((1 : ℚ) ⊗ₜ[ℤ] o) :=
    GlobalTheory.T.exists_tensorPadicInt_equiv_adjoin_of_free_finite G.O p
  obtain ⟨κ, hκ⟩ := GlobalTheory.T.exists_ringOfIntegersTensorPadic_equiv_adjoin G.F p
  let Φ : G.O ⊗[ℤ] ℤ_[p] ≃+* Matrix (Fin G.m) (Fin G.m) (𝓞 G.F ⊗[ℤ] ℤ_[p]) :=
    ι.trans (ψ.toRingEquiv.trans κ.symm.mapMatrix)
  refine ⟨AlgEquiv.ofRingEquiv (f := Φ) fun c => ?_⟩
  obtain ⟨h, hh⟩ := hψ (κ (c ⊗ₜ[ℤ] 1))
  have e1 : ι (algebraMap (𝓞 G.F) (G.O ⊗[ℤ] ℤ_[p]) c) = ⟨_, h⟩ := by
    apply Subtype.ext
    show (ι (algebraMap (𝓞 G.F) (G.O ⊗[ℤ] ℤ_[p]) c) : ℚ_[p] ⊗[ℚ] (ℚ ⊗[ℤ] G.O)) =
      cenMap p G.F (ℚ ⊗[ℤ] G.O) (κ (c ⊗ₜ[ℤ] 1) : ℚ_[p] ⊗[ℚ] G.F)
    rw [Algebra.TensorProduct.algebraMap_apply, hι, hκ, cenMap, Algebra.TensorProduct.map_tmul]
    show _ = (1 : ℚ_[p]) ⊗ₜ[ℚ] algebraMap G.F (ℚ ⊗[ℤ] G.O) (c : G.F)
    rw [algebraMap_F_coe]
  show κ.symm.mapMatrix (ψ (ι _)) = _
  rw [e1]
  erw [hh]
  ext i j
  simp [Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.algebraMap_eq_diagonal]
  split_ifs <;> simp [RingEquiv.symm_apply_apply]

end GlobalTheory.UPel.HT.Gen.SplitAE
end

section

open CategoryTheory AlgebraicGeometry Limits TopologicalSpace Opposite GlobalTheory SheafPull

noncomputable section

namespace GlobalTheory.Cube.PullHom

variable {ι κ : Type} [LinearOrder ι] [LinearOrder κ] {R S : Type} [Ring R] [Ring S]
  {σ : R →+* S} {τ : κ → ι} {A : Cube.{0} ι R} {B : Cube.{0} κ S} (ψ : Cube.PullHom σ τ A B)


open Classical in
def totalPull (y : ∀ s : Finset ι, A.obj s) (s : Finset κ) : B.obj s :=
  if Set.InjOn τ (s : Set κ) then PD.sortSign τ s • ψ.app s (y (s.image τ)) else 0

theorem term_eq_totalPull {p : ℕ} (x : Cube.Term A p) (s : {s : Finset κ // s.card = p}) :
    ψ.term p x s = totalPull ψ (Cube.extend A p x) s.1 := by
  by_cases h : Set.InjOn τ (s.1 : Set κ)
  · rw [term_apply_of_injOn ψ x s h, totalPull, if_pos h, Cube.extend_apply_of_eq A x (card_image s h)]
  · rw [term_apply_of_not_injOn ψ x s h, totalPull, if_neg h]

theorem totalPull_totalD (y : ∀ s : Finset ι, A.obj s) :
    totalPull ψ (Cube.totalD A y) = Cube.totalD B (totalPull ψ y) := by
  funext t
  rw [Cube.totalD_apply B]
  by_cases h : Set.InjOn τ (t : Set κ)

  · rw [totalPull, if_pos h, Cube.totalD_apply A,
    Finset.sum_image (fun x hx y hy hxy => h hx hy hxy), map_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hi' : Set.InjOn τ ((t.erase i : Finset κ) : Set κ) :=
      h.mono (Finset.coe_subset.2 (Finset.erase_subset i t))
    rw [totalPull, if_pos hi', map_zsmul, map_zsmul, smul_smul, smul_smul,
      PD.PullMap.sign_inj h hi, ← ψ.app_res]
    congr 2
    exact Cube.res_congr A y (PD.PullMap.image_erase_of_injOn h hi) _ _
  · rw [totalPull, if_neg h]
    obtain ⟨a, ha, b, hb, he, hab⟩ : ∃ a ∈ t, ∃ b ∈ t, τ a = τ b ∧ a ≠ b := by
      by_contra hc
      push_neg at hc
      exact h (fun x hx y hy hxy => hc x hx y hy hxy)
    have zero_of : ∀ s : Finset κ, a ∈ s → b ∈ s → totalPull ψ y s = 0 := fun s has hbs => by
      rw [totalPull, if_neg]
      intro hs
      exact hab (hs has hbs he)
    rw [Finset.sum_eq_add_of_mem a b ha hb hab (fun x _ hne => by
      rw [zero_of _ (Finset.mem_erase.2 ⟨hne.1.symm, ha⟩) (Finset.mem_erase.2 ⟨hne.2.symm, hb⟩),
        map_zero, smul_zero])]
    by_cases hia : Set.InjOn τ ((t.erase a : Finset κ) : Set κ)
    · have hib := PD.PullMap.injOn_erase_swap hb hab he hia
      have key : ∀ c ∈ t, (t.erase c).image τ = t.image τ →
          Cube.res B (Finset.erase_subset c t) (ψ.app (t.erase c) (y ((t.erase c).image τ))) =
            ψ.app t (y (t.image τ)) := by
        intro c _ e
        rw [← ψ.app_res, Cube.res_congr A y e _ (subset_refl _), Cube.res_self]
      rw [totalPull, totalPull, if_pos hia, if_pos hib, map_zsmul, map_zsmul,
        key a ha (PD.PullMap.image_erase_eq hb hab he),
        key b hb (PD.PullMap.image_erase_eq ha hab.symm he.symm), smul_smul, smul_smul, ← add_smul,
        PD.PullMap.sign_pair ha hb hab he hia, neg_add_cancel, zero_smul]
    · have hib : ¬ Set.InjOn τ ((t.erase b : Finset κ) : Set κ) := fun hib =>
        hia (PD.PullMap.injOn_erase_swap ha hab.symm he.symm hib)
      rw [totalPull, totalPull, if_neg hia, if_neg hib, map_zero, map_zero, smul_zero, smul_zero,
        add_zero]

theorem term_d (p : ℕ) (x : Cube.Term A p) :
    ψ.term (p + 1) (Cube.d A p x) = Cube.d B p (ψ.term p x) := by
  funext t
  rw [Cube.d_apply_eq_totalD B (ψ.term p x) (totalPull ψ (Cube.extend A p x))
    (fun s => term_eq_totalPull ψ x s), ← totalPull_totalD]
  by_cases h : Set.InjOn τ (t.1 : Set κ)
  · rw [term_apply_of_injOn ψ _ t h, totalPull, if_pos h, Cube.d_apply_eq_totalD A x (Cube.extend A p x)
      (fun s => (Cube.extend_apply_of_eq A x s.2).symm)]
  · rw [term_apply_of_not_injOn ψ _ t h, totalPull, if_neg h]

end GlobalTheory.Cube.PullHom
end
end

section

open CategoryTheory AlgebraicGeometry Limits TopologicalSpace Opposite GlobalTheory SheafPull

namespace GlobalTheory

theorem cechAbPull_degZero : ∀ {T T' : TopCat.{0}} (f : T' ⟶ T) {ι κ : Type} [LinearOrder ι] [LinearOrder κ]
    [Finite ι] [Finite κ] {V : Opens T} {U : ι → Opens T} {V' : Opens T'} {U' : κ → Opens T'}
    (τ : κ → ι) (hτ : ∀ s : Finset κ, cechOpen V' U' s ≤ (Opens.map f).obj (cechOpen V U (s.image τ)))
    (hc : V ≤ ⨆ i, U i) (hc' : V' ≤ ⨆ k, U' k) (hV : V' ≤ (Opens.map f).obj V)
    {F : AbSheaf T} {G : AbSheaf T'} (φ : F ⟶ (push f).obj G) (hF : CechAcyclic V U F)
    (hG : CechAcyclic V' U' G) (x : LinearMap.ker (Cube.d (cechAbCube F.obj V U) (0 + 1)))
    (y : LinearMap.ker (Cube.d (cechAbCube G.obj V' U') (0 + 1))),
    y.1 = (cechAbPull f τ hτ φ).term (0 + 1) x.1 →
    cechAbHEquivH' hc' hG 0 (cechClass _ 0 y) =
      SheafPull.pull f φ 0 (homOfLE hV) (cechAbHEquivH' hc hF 0 (cechClass _ 0 x)) := by
  intro T T' f ι κ _ _ _ _ V U V' U' τ hτ hc hc' hV F G φ hF hG x y hy
  obtain ⟨s, hs⟩ := (cechAbHZeroEquiv F.property hc).symm.surjective (cechClass _ 0 x)
  rw [cechAbHZeroEquiv_symm_apply] at hs
  have h1 : cechClass (cechAbCube F.obj V U) 0
      ⟨presheafCechAug (F.obj ⋙ abToIntModule) V U s,
        LinearMap.mem_ker.2 (d_presheafCechAug (F.obj ⋙ abToIntModule) V U s)⟩ =
      cechClass _ 0 x := (presheafToCechH_apply (F.obj ⋙ abToIntModule) V U s).symm.trans hs
  have hx : x.1 = presheafCechAug (F.obj ⋙ abToIntModule) V U s :=
    (congrArg Subtype.val ((cechClass_zero_bijective _).1 h1)).symm
  obtain ⟨s'', hs''⟩ : ∃ s'', s'' = G.obj.map (homOfLE hV).op (φ.hom.app (op V) s) := ⟨_, rfl⟩
  have hy' : y.1 = presheafCechAug (G.obj ⋙ abToIntModule) V' U' s'' := by
    funext t
    obtain ⟨t, ht⟩ := t
    obtain ⟨k, rfl⟩ := Finset.card_eq_one.1 ht
    rw [hy, Cube.PullHom.term_apply_of_injOn _ _ _ (by simp)]
    have hsg : PD.sortSign τ {k} = 1 := by simp [PD.sortSign]
    rw [hsg, one_smul]
    show G.obj.map (homOfLE (hτ {k})).op (φ.hom.app (op (cechOpen V U (({k} : Finset κ).image τ)))
      (x.1 ⟨({k} : Finset κ).image τ, Cube.PullHom.card_image ⟨{k}, ht⟩ (by simp)⟩)) =
      G.obj.map (homOfLE (cechOpen_le V' U' {k})).op s''
    rw [hx, hs'']
    have nat := ConcreteCategory.congr_hom
      (φ.hom.naturality (homOfLE (cechOpen_le V U (({k} : Finset κ).image τ))).op) s
    change φ.hom.app _ (F.obj.map _ s) = G.obj.map _ (φ.hom.app _ s) at nat
    change G.obj.map _ (φ.hom.app _ (F.obj.map (homOfLE (cechOpen_le V U (({k} : Finset κ).image τ))).op s)) = _
    rw [nat]
    refine (ConcreteCategory.congr_hom (G.obj.map_comp _ _) _).symm.trans
      (Eq.trans ?_ (ConcreteCategory.congr_hom (G.obj.map_comp _ _) _))
    rfl
  have h2 : cechClass _ 0 y = toCechAbH G.obj V' U' s'' :=
    (congrArg (cechClass _ 0) (Subtype.ext hy')).trans
      (presheafToCechH_apply (G.obj ⋙ abToIntModule) V' U' s'').symm
  rw [h2, ← hs, cechAbHEquivH'_toCechAbH, cechAbHEquivH'_toCechAbH]
  apply (SheafLES.equivZero G V').injective
  rw [AddEquiv.apply_symm_apply, SheafPull.equivZero_pull, AddEquiv.apply_symm_apply, hs'']

end GlobalTheory
end

section

noncomputable section

namespace GlobalTheory.ExpAtTypePrimes

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G NumberField IsDedekindDomain

theorem col_smul {R : Ranks} {ι : Type} [Fintype ι] {hc : ι → HCParam R} (C : ColumnChain R ι hc) (a : ℂ)
    (φ : C.cls 0 → C.Y 0 → ℂ) : C.col (a • φ) = a • C.col φ := by
  unfold ColumnChain.col
  generalize R.m = n
  induction n with
  | zero => rfl
  | succ n ih =>
    funext j
    simp only [Formalism.ThetaLiftIndependence.chainOpM, Formalism.ThetaLiftIndependence.kerOpM, ih, Pi.smul_apply, map_smul, Finset.smul_sum]
    exact Finset.sum_congr rfl fun i _ => smul_comm _ _ _

theorem perCol_smul (D : D7) (u : D.what₂.Word) (μ : D.what₂.Tup) (a : ℂ) (φ : D.what₂.Mu u) (F : D.what₂.Amb μ) :
    D.what₂.perCol u μ (a • φ) F = a * D.what₂.perCol u μ φ F := by
  by_cases hμ : μ = D.what₂.mu0
  · subst hμ
    simp only [D.perCol_base_eq_PtilCol, PeriodMap.PtilCol, PeriodMap.Ptil, map_smul, Submodule.coe_smul, col_smul,
      LinearMap.smul_apply, smul_eq_mul]
  · simp only [D.perCol_tie u μ hμ, PeriodMap.PtilCol, PeriodMap.Ptil, map_smul, Submodule.coe_smul, col_smul,
      LinearMap.smul_apply, smul_eq_mul]

end GlobalTheory.ExpAtTypePrimes

end
end
