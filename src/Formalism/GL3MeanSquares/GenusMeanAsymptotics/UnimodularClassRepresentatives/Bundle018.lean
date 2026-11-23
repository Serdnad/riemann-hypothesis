module

public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.AlgebraMapConjO
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle013
public import Formalism.HermitianLattices.HermitianLatticesProofs.TraceReal
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle015
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle009
public import Formalism.HermitianLattices.HermitianLatticesProofs.AutFinite
import Formalism.HermitianLattices.HermitianLatticesProofs.IsomAct
public import Formalism.ThetaLiftIndependence.ThetaOrbitSums.ClassRepsDefinite
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle017
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.DifferentIdealEqTop
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.LocalDensityRatio
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExtPPowLeSpanSup
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.BallB

variable {K : Type} [Field K] [NumberField K] [StarRing K]
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem exists_orth_basis_mem [FiniteDimensional K V] (hK : Formalism.HermitianLatticesTheory.IsCMUnram K)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsFullLattice K L) :
    ∃ b : Basis (Fin (finrank K V)) K V, (∀ i, b i ∈ L) ∧ ∀ i j, i ≠ j → h (b i) (b j) = 0 := by
  obtain ⟨e, he, -⟩ := orthBasisPos K hK V h hs hd
  choose n hn hnx using fun i => Formalism.HermitianLatticesTheory.traceReal_mult L hL (e i)
  have hb : ∀ i, e.unitsSMul (fun i => Units.mk0 (n i : K) (Int.cast_ne_zero.2 (hn i))) i =
      (n i : K) • e i := fun i => by rw [Basis.unitsSMul_apply]; rfl
  refine ⟨e.unitsSMul fun i => Units.mk0 (n i : K) (Int.cast_ne_zero.2 (hn i)), fun i => ?_,
    fun i j hij => ?_⟩
  · rw [hb, Int.cast_smul_eq_zsmul]; exact hnx i
  · simp only [hb, map_smulₛₗ, LinearMap.smul_apply, he i j hij, smul_zero]

omit [NumberField K] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] in
theorem form_eq {ι : Type*} [Fintype ι] [DecidableEq ι] {h : V →ₗ⋆[K] V →ₗ[K] K} (b : Basis ι K V)
    (ho : ∀ i j, i ≠ j → h (b i) (b j) = 0) (x : V) :
    h x x = ∑ i, star (b.repr x i) * b.repr x i * h (b i) (b i) := by
  conv_lhs => rw [← b.sum_repr x]

  simp only [map_sum, LinearMap.sum_apply, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul,
  starRingEnd_apply, RingHom.id_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single i]
  · ring
  · intro j _ hj
    simp [ho j i hj]
  · intro hi; exact absurd (Finset.mem_univ i) hi

omit [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] in
theorem re_form_eq (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {ι : Type*} [Fintype ι] [DecidableEq ι]
    {h : V →ₗ⋆[K] V →ₗ[K] K} (b : Basis ι K V) (ho : ∀ i j, i ≠ j → h (b i) (b j) = 0) (x : V)
    (φ : K →+* ℂ) :
    (φ (h x x)).re = ∑ i, (φ (h (b i) (b i))).re * Complex.normSq (φ (b.repr x i)) := by

  rw [form_eq b ho x, map_sum, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, map_mul, hK.2.1, ← Complex.normSq_eq_conj_mul_self, Complex.re_ofReal_mul, mul_comm]

omit [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] in
theorem forall_embedding_iff (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {ι : Type*} [Fintype ι] [DecidableEq ι]
    {h : V →ₗ⋆[K] V →ₗ[K] K} (b : Basis ι K V) (ho : ∀ i j, i ≠ j → h (b i) (b j) = 0) (x : V)
    (T : ℝ) :
    (∀ φ : K →+* ℂ, (φ (h x x)).re ≤ T) ↔ ∀ w : {w : InfinitePlace K // w.IsComplex},
      ∑ i, (w.1.embedding (h (b i) (b i))).re * Complex.normSq (w.1.embedding (b.repr x i)) ≤ T := by
  have : IsTotallyComplex K := hK.1
  constructor
  · intro hφ w
    rw [← re_form_eq hK b ho]
    exact hφ _
  · intro hw φ
    have h1 := hw ⟨InfinitePlace.mk φ, IsTotallyComplex.isComplex _⟩
    rw [← re_form_eq hK b ho] at h1
    rcases InfinitePlace.embedding_mk_eq φ with h2 | h2
    · rwa [h2] at h1
    · rwa [h2, ComplexEmbedding.conjugate_coe_eq, Complex.conj_re] at h1

theorem gdet_eq_prod {h : V →ₗ⋆[K] V →ₗ[K] K} (b : Basis (Fin (finrank K V)) K V)
    (ho : ∀ i j, i ≠ j → h (b i) (b j) = 0) : gdet h b = ∏ i, h (b i) (b i) := by
  unfold gdet
  rw [← Matrix.det_diagonal]
  congr 1
  ext i j
  by_cases hij : i = j
  · subst hij; simp
  · simp [hij, ho i j hij]

omit [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] in
theorem place_form_eq (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm)
    (hd : IsTotPosDef h) {x : V} (hx : x ≠ 0) (w : InfinitePlace K) :
    w (h x x) = (w.embedding (h x x)).re := by
  have h1 : star (h x x) = h x x := hs.eq x x
  have h2 : (w.embedding (h x x)).im = 0 := by
    rw [← Complex.conj_eq_iff_im, ← hK.2.1, h1]
  rw [← InfinitePlace.norm_embedding_eq, ← Complex.abs_re_eq_norm.2 h2,
    abs_of_pos (hd x hx w.embedding)]

open scoped Classical in
theorem prod_place_gdet (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm)
    (hd : IsTotPosDef h) (b : Basis (Fin (finrank K V)) K V)
    (ho : ∀ i j, i ≠ j → h (b i) (b j) = 0) :
    ∏ w : InfinitePlace K, w (gdet h b) =
      ∏ w : {w : InfinitePlace K // w.IsComplex}, ∏ i, (w.1.embedding (h (b i) (b i))).re := by
  have : IsTotallyComplex K := hK.1
  rw [← (Equiv.subtypeUnivEquiv (fun w : InfinitePlace K => IsTotallyComplex.isComplex w)).prod_comp]
  refine Finset.prod_congr rfl fun w _ => ?_
  rw [gdet_eq_prod b ho, map_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  exact place_form_eq hK hs hd (b.ne_zero i) _

theorem isLattice_span [FiniteDimensional K V] (b : Basis (Fin (finrank K V)) K V) :
    Submodule.IsLattice K (Submodule.span (𝓞 K) (Set.range b)) :=
  Submodule.IsLattice.of_fg K ⟨(Set.finite_range b).toFinset, by rw [Set.Finite.coe_toFinset]⟩
end Formalism.HermitianLattices.Ext.L3.BallB
end
end

section

open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3

namespace StabilizerLattices

variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

variable {h : V →ₗ⋆[K] V →ₗ[K] K}

omit [FiniteDimensional K V] in
theorem exists_smul_iff (N M : Submodule (𝓞 K) V) :
    (∃ g : Formalism.HermitianLatticesTheory.isom h, g • N = M) ↔ ∃ g ∈ Formalism.HermitianLatticesTheory.isom h, Formalism.HermitianLatticesTheory.gmap g N = M := by
  constructor
  · rintro ⟨g, hg⟩
    exact ⟨g.1, g.2, hg⟩
  · rintro ⟨g, hg, e⟩
    exact ⟨⟨g, hg⟩, e⟩

theorem finite_rep (hd : IsTotPosDef h) {M : Submodule (𝓞 K) V} (hM : Submodule.IsLattice K M)
    (n : K) : {x : V | x ∈ M ∧ h x x = n}.Finite := by
  have := hM
  refine (Formalism.HermitianLatticesTheory.autFinite_short h (trace_pos hd) M (Algebra.trace ℚ K n)).subset ?_
  rintro x ⟨hx, rfl⟩
  exact ⟨hx, le_rfl⟩

theorem finite_stab_lat (hs : h.IsSymm) (hd : IsTotPosDef h) {M : Submodule (𝓞 K) V}
    (hM : Submodule.IsFullLattice K M) :
    (MulAction.stabilizer (Formalism.HermitianLatticesTheory.isom h) M : Set (Formalism.HermitianLatticesTheory.isom h)).Finite := by
  have : Finite (Formalism.ThetaLiftIndependence.autL h M) := (Formalism.HermitianLatticesTheory.autFinite K V h hs (trace_pos hd) M hM).to_subtype
  have : Finite (MulAction.stabilizer (Formalism.HermitianLatticesTheory.isom h) M) := Finite.of_equiv _ (stabLatEquiv M).symm
  exact Set.toFinite _

theorem exists_classReps (hs : h.IsSymm) (hd : IsTotPosDef h) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsLattice K L) : ∃ s, Formalism.ThetaLiftIndependence.IsClassReps h L s :=
  (Formalism.ThetaLiftIndependence.classRepsDefinite K V h hs (trace_pos hd) L hL).1

theorem exists_pairReps (hs : h.IsSymm) (hd : IsTotPosDef h) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsLattice K L) (n : K) :
    ∃ sX : Finset (Submodule (𝓞 K) V × V), (∀ t ∈ sX, t ∈ pairs h L n) ∧
      ∀ p ∈ pairs h L n, ∃! t, t ∈ sX ∧ ∃ g : Formalism.HermitianLatticesTheory.isom h, g • t = p := by
  obtain ⟨s, hs1, hs2⟩ := exists_classReps hs hd hL
  refine OrbSum.exists_reps_of_cover (pairs h L n) (pairs_stable hs L n)
    (⋃ M ∈ s, (fun x => (M, x)) '' {x : V | x ∈ M ∧ h x x = n}) ?_ ?_ ?_
  · exact Set.Finite.biUnion s.finite_toSet fun M hM => (finite_rep hd (hs1 M hM).1.toIsLattice n).image _
  · intro c hc
    obtain ⟨M, hM, x, hx, rfl⟩ := Set.mem_iUnion₂.mp hc
    exact ⟨hs1 M hM, hx.1, hx.2⟩
  · intro p hp
    obtain ⟨M, ⟨hM, g, hg, hgM⟩, -⟩ := hs2 p.1 hp.1
    refine ⟨(M, g.symm p.2), Set.mem_iUnion₂.mpr ⟨M, hM, g.symm p.2, ⟨?_, ?_⟩, rfl⟩, ⟨g, hg⟩, ?_⟩
    · rw [← Formalism.HermitianLatticesTheory.isomAct_mem_gmap, hgM]
      exact hp.2.1
    · rw [SplitBAux.symm_mem_isom hg]
      exact hp.2.2
    · exact Prod.ext hgM (LinearEquiv.apply_symm_apply g p.2)

theorem sum_pairs_eq_rep (hs : h.IsSymm) (hd : IsTotPosDef h) {L : Submodule (𝓞 K) V} (n : K)
    {s : Finset (Submodule (𝓞 K) V)} (hsr : Formalism.ThetaLiftIndependence.IsClassReps h L s)
    {sX : Finset (Submodule (𝓞 K) V × V)} (hsX : ∀ t ∈ sX, t ∈ pairs h L n)
    (hX : ∀ p ∈ pairs h L n, ∃! t, t ∈ sX ∧ ∃ g : Formalism.HermitianLatticesTheory.isom h, g • t = p) :
    ∑ t ∈ sX, ((Nat.card (MulAction.stabilizer (Formalism.HermitianLatticesTheory.isom h) t) : ℕ) : ℝ)⁻¹ =
      ∑ M ∈ s, (repCount h M n : ℝ) / ((Nat.card (Formalism.ThetaLiftIndependence.autL h M) : ℕ) : ℝ) := by
  have key := OrbSum.sum_orbits_on (G := Formalism.HermitianLatticesTheory.isom h) (Prod.fst : Submodule (𝓞 K) V × V → _)
    (fun _ _ => rfl) (pairs h L n) (Formalism.HermitianLatticesTheory.genus h L) (pairs_stable hs L n) (fun p hp => hp.1)
    sX s hsX hsr.1 hX (fun M hM => by simp_rw [exists_smul_iff]; exact hsr.2 M hM)
    (fun M hM => finite_stab_lat hs hd hM.1)
  rw [key]
  refine Finset.sum_congr rfl fun M hM => ?_
  have e1 : Nat.card {p : Submodule (𝓞 K) V × V // p ∈ pairs h L n ∧ p.1 = M} = repCount h M n :=
    Nat.card_congr
      { toFun := fun p => ⟨p.1.2, (congrArg (fun N : Submodule (𝓞 K) V => p.1.2 ∈ N) p.2.2).mp p.2.1.2.1, p.2.1.2.2⟩
        invFun := fun x => ⟨(M, x.1), ⟨hsr.1 M hM, x.2.1, x.2.2⟩, rfl⟩
        left_inv := fun p => Subtype.ext (Prod.ext p.2.2.symm rfl)
        right_inv := fun _ => rfl }
  rw [e1, Nat.card_congr (stabLatEquiv M)]

end StabilizerLattices

end Formalism.HermitianLattices.Ext.L3
end
end

section

open NumberField Module
open scoped Classical

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.BoxCube

open BoxSum

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]

theorem absNorm_le_of_mem_ideal {b : Ideal (𝓞 F)} {n : 𝓞 F} (hn : n ∈ b) (h0 : n ≠ 0) :
    (Ideal.absNorm b : ℝ) ≤ (Ideal.absNorm (Ideal.span {n}) : ℝ) := by
  have h1 : Ideal.absNorm b ∣ Ideal.absNorm (Ideal.span {n}) :=
    Ideal.absNorm_dvd_absNorm_of_le ((Ideal.span_singleton_le_iff_mem b).2 hn)
  have h2 : Ideal.absNorm (Ideal.span {n}) ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
    exact h0
  exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero h2) h1

theorem absNorm_le_pow (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {b : Ideal (𝓞 F)} {T : ℝ}
    {n : 𝓞 F} (hn : n ∈ boxSet K F T) (hb : n ∈ b) :
    (Ideal.absNorm b : ℝ) ≤ T ^ Formalism.HermitianLatticesTheory.fDeg K :=
  (absNorm_le_of_mem_ideal hb (ne_zero_of_mem_boxSet hn)).trans (absNorm_le_of_mem hK hF hn)

theorem eq_of_close (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {b : Ideal (𝓞 F)} {δ : ℝ}
    (hδ : δ ^ Formalism.HermitianLatticesTheory.fDeg K ≤ (Ideal.absNorm b : ℝ)) {n n' : 𝓞 F} (hn : n ∈ b) (hn' : n' ∈ b)
    (hc : ∀ w : {w : InfinitePlace F // w.IsReal}, |rEmb w n - rEmb w n'| < δ) : n = n' := by
  have hR : IsTotallyReal F := QuadraticExtensionConjugation.isTotallyReal hK hF
  by_contra hne
  have h0 : n - n' ≠ 0 := sub_ne_zero.2 hne
  have h1 := absNorm_le_of_mem_ideal (b.sub_mem hn hn') h0
  rw [absNorm_eq_prod] at h1
  have hne' : (Finset.univ : Finset {w : InfinitePlace F // w.IsReal}).Nonempty := by
    obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
    exact ⟨⟨w, IsTotallyReal.isReal w⟩, Finset.mem_univ _⟩
  have h2 : ∏ w : {w : InfinitePlace F // w.IsReal}, |rEmb w (n - n')| <
      ∏ _w : {w : InfinitePlace F // w.IsReal}, δ := by
    refine Finset.prod_lt_prod_of_nonempty₀ (fun w _ => ?_) (fun w _ => ?_) hne'
    · rw [abs_pos]
      intro h3
      apply h0
      have : (InfinitePlace.embedding_of_isReal w.2) ((n - n' : 𝓞 F) : F) = 0 := h3
      rw [map_eq_zero] at this
      exact RingOfIntegers.coe_injective (by simpa using this)
    · rw [map_sub]
      exact hc w
  rw [Finset.prod_const, Finset.card_univ, card_real hK hF] at h2
  linarith

theorem abs_sub_lt_of_floor_eq {δ a a' : ℝ} (hδ : 0 < δ) (ha : 0 ≤ a) (ha' : 0 ≤ a')
    (h : ⌊a / δ⌋₊ = ⌊a' / δ⌋₊) : |a - a'| < δ := by
  have h1 := Nat.floor_le (div_nonneg ha hδ.le)
  have h2 := Nat.lt_floor_add_one (a / δ)
  have h3 := Nat.floor_le (div_nonneg ha' hδ.le)
  have h4 := Nat.lt_floor_add_one (a' / δ)
  rw [h] at h1 h2
  have h5 : a / δ - a' / δ < 1 := by linarith
  have h6 : a' / δ - a / δ < 1 := by linarith
  rw [← sub_div, div_lt_one hδ] at h5 h6
  rw [abs_lt]
  constructor <;> linarith

theorem card_le_pow (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {b : Ideal (𝓞 F)} {δ T : ℝ}
    (hδ0 : 0 < δ) (hδ : δ ^ Formalism.HermitianLatticesTheory.fDeg K ≤ (Ideal.absNorm b : ℝ)) :
    Nat.card {n : 𝓞 F // n ∈ boxSet K F T ∧ n ∈ b} ≤ (⌊T / δ⌋₊ + 1) ^ Formalism.HermitianLatticesTheory.fDeg K := by
  let W := {w : InfinitePlace F // w.IsReal}
  let g : {n : 𝓞 F // n ∈ boxSet K F T ∧ n ∈ b} → (W → Fin (⌊T / δ⌋₊ + 1)) := fun n w =>
    ⟨⌊rEmb w n.1 / δ⌋₊, Nat.lt_succ_of_le (Nat.floor_le_floor
      (div_le_div_of_nonneg_right (((mem_boxSet_iff hK hF).1 n.2.1) w).2 hδ0.le))⟩
  have hg : Function.Injective g := by
    intro n n' h
    refine Subtype.ext (eq_of_close hK hF hδ n.2.2 n'.2.2 fun w => ?_)
    have h1 : ⌊rEmb w n.1 / δ⌋₊ = ⌊rEmb w n'.1 / δ⌋₊ := congrArg Fin.val (congrFun h w)
    exact abs_sub_lt_of_floor_eq hδ0 (((mem_boxSet_iff hK hF).1 n.2.1) w).1.le
      (((mem_boxSet_iff hK hF).1 n'.2.1) w).1.le h1
  have h1 := Nat.card_le_card_of_injective g hg
  have h2 : Nat.card (W → Fin (⌊T / δ⌋₊ + 1)) = (⌊T / δ⌋₊ + 1) ^ Formalism.HermitianLatticesTheory.fDeg K := by
    rw [Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_fin, card_real hK hF]
  rwa [h2] at h1

theorem fDeg_pos : 0 < Formalism.HermitianLatticesTheory.fDeg K := Fintype.card_pos

theorem card_box_le (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {b : Ideal (𝓞 F)}
    (hb : b ≠ ⊥) {T : ℝ} (hT0 : 0 ≤ T) :
    (Nat.card {n : 𝓞 F // n ∈ boxSet K F T ∧ n ∈ b} : ℝ) ≤
      2 ^ Formalism.HermitianLatticesTheory.fDeg K * T ^ Formalism.HermitianLatticesTheory.fDeg K / (Ideal.absNorm b : ℝ) := by
  have hf : Formalism.HermitianLatticesTheory.fDeg K ≠ 0 := (fDeg_pos (K := K)).ne'
  have hN : (0 : ℝ) < (Ideal.absNorm b : ℝ) := by
    have : Ideal.absNorm b ≠ 0 := by rwa [Ne, Ideal.absNorm_eq_zero_iff]
    exact_mod_cast Nat.pos_of_ne_zero this
  by_cases he : IsEmpty {n : 𝓞 F // n ∈ boxSet K F T ∧ n ∈ b}
  · rw [Nat.card_of_isEmpty, Nat.cast_zero, ← mul_pow]
    positivity
  rw [not_isEmpty_iff] at he
  obtain ⟨n, hn, hnb⟩ := he
  have hT : 0 < T := by
    obtain ⟨φ⟩ : Nonempty (K →+* ℂ) := inferInstance
    exact (hn φ).1.trans_le (hn φ).2
  set δ : ℝ := (Ideal.absNorm b : ℝ) ^ ((Formalism.HermitianLatticesTheory.fDeg K : ℝ)⁻¹) with hδdef
  have hδ0 : 0 < δ := Real.rpow_pos_of_pos hN _
  have hδ : δ ^ Formalism.HermitianLatticesTheory.fDeg K = (Ideal.absNorm b : ℝ) := Real.rpow_inv_natCast_pow hN.le hf
  have hδT : δ ≤ T := by
    have := absNorm_le_pow hK hF hn hnb
    rw [← hδ] at this
    exact (pow_le_pow_iff_left₀ hδ0.le hT.le hf).1 this
  have h1 := card_le_pow hK hF (T := T) hδ0 hδ.le
  have h2 : ((⌊T / δ⌋₊ + 1 : ℕ) : ℝ) ≤ 2 * T / δ := by
    have h3 := Nat.floor_le (div_nonneg hT.le hδ0.le)
    have h4 : 1 ≤ T / δ := (one_le_div hδ0).2 hδT
    push_cast
    rw [mul_div_assoc]
    linarith
  calc (Nat.card {n : 𝓞 F // n ∈ boxSet K F T ∧ n ∈ b} : ℝ)
      ≤ (((⌊T / δ⌋₊ + 1) ^ Formalism.HermitianLatticesTheory.fDeg K : ℕ) : ℝ) := by exact_mod_cast h1
    _ = ((⌊T / δ⌋₊ + 1 : ℕ) : ℝ) ^ Formalism.HermitianLatticesTheory.fDeg K := by push_cast; rfl
    _ ≤ (2 * T / δ) ^ Formalism.HermitianLatticesTheory.fDeg K := pow_le_pow_left₀ (by positivity) h2 _
    _ = _ := by rw [div_pow, mul_pow, hδ]

end Formalism.HermitianLattices.Ext.L3.BoxCube
end
end

section

open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]

theorem exists_add_conj_eq (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (a : 𝓞 F) :
    ∃ z : 𝓞 K, z + conjO K z = algebraMap (𝓞 F) (𝓞 K) a := by
  let ι := algebraMap (𝓞 F) (𝓞 K)
  have coe_ι (b : 𝓞 F) : ((ι b : 𝓞 K) : K) = algebraMap F K (b : F) :=
    (IsScalarTower.algebraMap_apply (𝓞 F) (𝓞 K) K b).symm.trans
      (IsScalarTower.algebraMap_apply (𝓞 F) F K b)
  have ι_injective : Function.Injective ι := by
    intro b c h
    apply RingOfIntegers.ext
    have hcoe := congrArg (fun z : 𝓞 K => (z : K)) h
    exact (algebraMap F K).injective ((coe_ι b).symm.trans (hcoe.trans (coe_ι c)))
  have conj_ι (b : 𝓞 F) : conjO K (ι b) = ι b := by
    apply RingOfIntegers.ext
    change star ((ι b : 𝓞 K) : K) = ((ι b : 𝓞 K) : K)
    rw [coe_ι]
    exact (hF _).mpr ⟨b, rfl⟩
  have exists_trace (z : 𝓞 K) : ∃ b : 𝓞 F, ι b = z + conjO K z := by
    let w : 𝓞 K := z + conjO K z
    have hw : star (w : K) = (w : K) := by
      change star ((z : K) + star (z : K)) = (z : K) + star (z : K)
      rw [star_add, star_star, add_comm]
    obtain ⟨b, hb⟩ := (hF _).mp hw
    have hb_int : IsIntegral ℤ b := by
      apply (isIntegral_algHom_iff (algebraMap F K).toIntAlgHom (algebraMap F K).injective).mp
      change IsIntegral ℤ (algebraMap F K b)
      rw [hb]
      exact RingOfIntegers.isIntegral_coe w
    refine ⟨⟨b, hb_int⟩, RingOfIntegers.ext ?_⟩
    exact (coe_ι ⟨b, hb_int⟩).trans hb
  let trace (z : 𝓞 K) : 𝓞 F := Classical.choose (exists_trace z)
  have trace_spec (z : 𝓞 K) : ι (trace z) = z + conjO K z :=
    Classical.choose_spec (exists_trace z)
  let tr : 𝓞 K →ₗ[𝓞 F] 𝓞 F :=
    { toFun := trace
      map_add' := by
        intro x y
        apply ι_injective
        rw [trace_spec, map_add, map_add, trace_spec, trace_spec]
        ring
      map_smul' := by
        intro b z
        apply ι_injective
        rw [RingHom.id_apply, smul_eq_mul, map_mul, trace_spec, trace_spec, Algebra.smul_def,
          map_mul, conj_ι]
        ring }
  have htop : LinearMap.range tr = ⊤ := by
    by_contra hne
    obtain ⟨𝔭, h𝔭, hle⟩ := Ideal.exists_le_maximal (LinearMap.range tr) hne
    obtain ⟨θ, hθ⟩ := idealPowerSpanBounds.exists_theta hK hF h𝔭
    have hmem : ∀ z : 𝓞 K, z + conjO K z ∈ extP K 𝔭 := fun z => by
      rw [← trace_spec]
      exact Ideal.mem_map_of_mem _ (hle ⟨z, rfl⟩)
    have h2 : (2 : 𝓞 K) ∈ extP K 𝔭 := by
      have := hmem 1
      rwa [map_one, one_add_one_eq_two] at this
    have hsq : (θ - conjO K θ) * (θ - conjO K θ) ∈ extP K 𝔭 := by
      have : (θ - conjO K θ) * (θ - conjO K θ) =
          (θ + conjO K θ) * (θ + conjO K θ) - 2 * (2 * (θ * conjO K θ)) := by ring
      rw [this]
      exact sub_mem (Ideal.mul_mem_left _ _ (hmem θ)) (Ideal.mul_mem_right _ _ h2)
    have hdiff : (θ - conjO K θ) ∈ extP K 𝔭 ^ 1 :=
      idealPowerSpanBounds.mem_of_unit_mul_mem hθ (by simpa only [pow_one] using hsq)
    have hone : (1 : 𝓞 K) ∈ extP K 𝔭 ^ 1 :=
      idealPowerSpanBounds.mem_of_unit_mul_mem hθ (by simpa only [mul_one] using hdiff)
    have hcomap : Ideal.comap ι (extP K 𝔭) = 𝔭 :=
      Ideal.comap_map_eq_self_of_faithfullyFlat 𝔭
    have hone_mem : (1 : 𝓞 F) ∈ 𝔭 := by
      rw [← hcomap, Ideal.mem_comap, map_one]
      simpa only [pow_one] using hone
    exact h𝔭.ne_top ((Ideal.eq_top_iff_one _).2 hone_mem)
  obtain ⟨z, hz⟩ : a ∈ LinearMap.range tr := htop ▸ Submodule.mem_top
  exact ⟨z, (trace_spec z).symm.trans (congrArg ι hz)⟩

end Formalism.HermitianLattices.Ext.L3
end
end
