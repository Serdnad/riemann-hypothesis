module

public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.StandardRankOneLatticeOfLocal
import Formalism.LocalToGlobal.Columns.Bundle029
import Development.AbelianVarietyTheory.Counterexamples.PlaceInjectivity.StandardDeterminantUnits
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.EmbHInjective
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
public import Formalism.LocalToGlobal.GroupLattices.AdmissibleAtGeneratorPlaces
public import Formalism.SharpRestriction.Divisibility.StatementFT.PeriodPointConditions
public import Formalism.SharpRestriction.Divisibility.HookProducts.AdmPerTw
import Formalism.SharpRestriction.Divisibility.OrbitPlaces
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Presheaf
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.Col Formalism.L2.Ker Formalism.MainNotions

noncomputable section

namespace GlobalTheory.RelDetIdeal

open GlobalTheory.CharValCompare GlobalTheory.Survey.StandardDeterminantUnits

section General

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}

def relDet (L L' : Submodule (𝓞 E) (Sp E n)) : Submodule (𝓞 E) E :=
  Submodule.span (𝓞 E) {x | ∃ A : Matrix (Fin n) (Fin n) E, (∀ v ∈ L, A.mulVec v ∈ L') ∧ x = A.det}

omit [StarRing E] in
theorem val_pos {P : HeightOneSpectrum (𝓞 E)} {a : E} (h : a ≠ 0) : 0 < P.valuation E a :=
  zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 h)

omit [StarRing E] in
theorem gen_mul {P : HeightOneSpectrum (𝓞 E)} {I J : Submodule (𝓞 E) E} {a b : E} (ha : Gen P I a) (hb : Gen P J b) :
    Gen P (I * J) (a * b) := by
  refine gen_of (mul_ne_zero ha.1 hb.1) ?_ fun x hx => ?_
  · obtain ⟨s, hs, h1⟩ := (ha.2 a).2 le_rfl
    obtain ⟨t, ht, h2⟩ := (hb.2 b).2 le_rfl
    refine ⟨s * t, P.asIdeal.primeCompl.mul_mem hs ht, ?_⟩
    rw [← smul_mul_smul_comm]
    exact Submodule.mul_mem_mul h1 h2
  · refine Submodule.mul_induction_on hx (fun m hm k hk => ?_) (fun x y hx hy => Valuation.map_add_le _ hx hy)
    rw [map_mul, map_mul]
    exact mul_le_mul' ((ha.2 m).1 (ThetaMove.mem_localization_of_mem P hm)) ((hb.2 k).1 (ThetaMove.mem_localization_of_mem P hk))

omit [StarRing E] in
theorem eq_of_gen {I J : Submodule (𝓞 E) E} (a b : HeightOneSpectrum (𝓞 E) → E) (ha : ∀ P, Gen P I (a P)) (hb : ∀ P, Gen P J (b P))
    (h : ∀ P : HeightOneSpectrum (𝓞 E), P.valuation E (a P) = P.valuation E (b P)) : I = J := by
  apply le_antisymm
  · intro x hx
    exact ThetaMove.mem_of_locP fun P => ((hb P).2 x).2 (h P ▸ ((ha P).2 x).1 (ThetaMove.mem_localization_of_mem P hx))
  · intro x hx
    exact ThetaMove.mem_of_locP fun P => ((ha P).2 x).2 ((h P).symm ▸ ((hb P).2 x).1 (ThetaMove.mem_localization_of_mem P hx))

omit [StarRing E] in
theorem gen_one (P : HeightOneSpectrum (𝓞 E)) : Gen P (1 : Submodule (𝓞 E) E) 1 :=
  ⟨one_ne_zero, fun x => by rw [mem_localization_one, intAt_iff, map_one]⟩

theorem gen_bar {P : HeightOneSpectrum (𝓞 E)} {I : Submodule (𝓞 E) E} {a : E} (ha : Gen (conjPrime₂ P) I a) :
    Gen P (barI I) (star a) := by
  have h0 : star a ≠ 0 := star_ne_zero.2 ha.1
  refine gen_of h0 ?_ fun x hx => ?_
  · obtain ⟨s, hs, h1⟩ := (ha.2 a).2 le_rfl
    refine ⟨cO E s, hs, ?_⟩
    show star (cO E s • star a) ∈ I
    rwa [Algebra.smul_def, algebraMap_cO, star_mul', star_star, star_star, ← Algebra.smul_def]
  · have h2 := (ha.2 (star x)).1 (ThetaMove.mem_localization_of_mem _ hx)
    have h3 : IntAt (conjPrime₂ P) (star x / a) := by
      rw [intAt_iff, map_div₀]
      exact div_le_one_of_le₀ h2 zero_le
    have h4 := intAt_iff.1 (intAt_star h3)
    rwa [conjP_conjP, star_div₀, star_star, map_div₀, div_le_one₀ (val_pos h0)] at h4

theorem gen_relDet {P : HeightOneSpectrum (𝓞 E)} {L L' : Submodule (𝓞 E) (Sp E n)} (hL : L.FG) {f f' : Sp E n ≃ₗ[E] Sp E n}
    (hf : IsFr P L f) (hf' : IsFr P L' f') : Gen P (relDet L L') (dt f' / dt f) := by
  classical
  refine gen_of (div_ne_zero (dt_ne _) (dt_ne _)) ?_ ?_
  · let g : Sp E n →ₗ[E] Sp E n := (f' : Sp E n →ₗ[E] Sp E n) ∘ₗ (f.symm : Sp E n →ₗ[E] Sp E n)
    have hg : ∀ v ∈ L, g v ∈ localization₂ P.asIdeal L' := fun v hv =>
      (hf' _).2 ((hf _).1 (by simpa using ThetaMove.mem_localization_of_mem P hv))
    obtain ⟨S, rfl⟩ := hL
    have : ∀ i : S, ∃ s : 𝓞 E, s ∉ P.asIdeal ∧ s • g i ∈ L' := fun i => hg i (Submodule.subset_span i.2)
    choose s hs hs' using this
    have hp : ∏ i, s i ∉ P.asIdeal := fun hm => by
      obtain ⟨y, _, h⟩ := (Ideal.IsPrime.prod_mem_iff (hp := P.isPrime)).1 hm
      exact hs y h
    refine ⟨(∏ i, s i) ^ n, P.asIdeal.primeCompl.pow_mem hp n, Submodule.subset_span
      ⟨algebraMap (𝓞 E) E (∏ i, s i) • LinearMap.toMatrix' g, fun v hv => ?_, ?_⟩⟩
    · rw [Matrix.smul_mulVec, LinearMap.toMatrix'_mulVec, algebraMap_smul]
      induction hv using Submodule.span_induction with
      | mem y hy =>
        rw [← Finset.prod_erase_mul _ s (Finset.mem_univ ⟨y, hy⟩), mul_smul]
        exact L'.smul_mem _ (hs' ⟨y, hy⟩)
      | zero => simp
      | add a b _ _ ha hb => rw [map_add (f := _), smul_add]; exact add_mem ha hb
      | smul c a _ ha =>
        rw [← algebraMap_smul E c a, map_smul, algebraMap_smul, smul_comm]
        exact L'.smul_mem _ ha
    · have e : LinearMap.det g = dt f' / dt f := by
        rw [eq_div_iff (dt_ne _), LinearMap.det_comp, dt_eq, dt_eq, mul_assoc, LinearEquiv.det_symm_mul_det, mul_one]
      rw [Matrix.det_smul, LinearMap.det_toMatrix', e, Algebra.smul_def, map_pow, Fintype.card_fin]
  · intro x hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨A, hA, rfl⟩ := hy
      have h1 := val_det_le_one (P := P)
        ((f'.symm : Sp E n →ₗ[E] Sp E n) ∘ₗ Matrix.toLin' A ∘ₗ (f : Sp E n →ₗ[E] Sp E n)) fun x hx => by
        rw [← hf']
        obtain ⟨s, hs, hx⟩ := (hf x).2 hx
        refine ⟨s, hs, ?_⟩
        have := hA _ hx
        rw [← algebraMap_smul E s (f x), Matrix.mulVec_smul, algebraMap_smul] at this
        simpa using this
      have h2 : A.det = dt f' / dt f *
          LinearMap.det ((f'.symm : Sp E n →ₗ[E] Sp E n) ∘ₗ Matrix.toLin' A ∘ₗ (f : Sp E n →ₗ[E] Sp E n)) := by
        have h3 := LinearEquiv.det_mul_det_symm f'
        have h4 := dt_ne f
        rw [LinearMap.det_comp, LinearMap.det_comp, LinearMap.det_toLin', ← dt_eq f]
        rw [← dt_eq f'] at h3
        field_simp
        linear_combination (-A.det) * h3
      rw [h2, map_mul]
      exact mul_le_of_le_one_right' h1
    | zero => simp
    | add a b _ _ ha hb => exact Valuation.map_add_le _ ha hb
    | smul c a _ ha =>
      rw [Algebra.smul_def, map_mul]
      exact le_trans (mul_le_of_le_one_left' (P.valuation_le_one (K := E) c)) ha

theorem relDet_mul {L L' L'' : Submodule (𝓞 E) (Sp E n)} (hL : Submodule.IsFullLattice E L)
    (hL' : Submodule.IsFullLattice E L') (hL'' : Submodule.IsFullLattice E L'') :
    relDet L L'' = relDet L L' * relDet L' L'' := by
  choose f hf using fun P => (DetChrL.frame_exists P hL : ∃ f, IsFr P L f)
  choose f' hf' using fun P => (DetChrL.frame_exists P hL' : ∃ f, IsFr P L' f)
  choose f'' hf'' using fun P => (DetChrL.frame_exists P hL'' : ∃ f, IsFr P L'' f)
  refine eq_of_gen _ _ (fun P => gen_relDet hL.fg (hf P) (hf'' P))
    (fun P => gen_mul (gen_relDet hL.fg (hf P) (hf' P)) (gen_relDet hL'.fg (hf' P) (hf'' P))) fun P => ?_
  congr 1
  have := dt_ne (f P)
  have := dt_ne (f' P)
  field_simp

theorem normOne_relDet {L L' : Submodule (𝓞 E) (Sp E n)} (hL : IsSdLat L) (hL' : IsSdLat L') : NormOne (relDet L L') := by
  refine ⟨barI (relDet L L'), fun _ => Iff.rfl, ?_⟩
  choose f hf using fun P => exists_isFr P hL
  choose f' hf' using fun P => exists_isFr P hL'
  have hg := fun P => gen_relDet hL.1.fg (hf P) (hf' P)
  refine eq_of_gen _ _ (fun P => gen_mul (hg P) (gen_bar (hg (conjPrime₂ P)))) gen_one fun P => ?_
  have h1 := val_dual hL (hf (conjPrime₂ P)) (f' := f P) (by rw [conjP_conjP]; exact hf P)
  have h2 := val_dual hL' (hf' (conjPrime₂ P)) (f' := f' P) (by rw [conjP_conjP]; exact hf' P)
  rw [conjP_conjP] at h1 h2
  rw [star_div₀, div_mul_div_comm, map_div₀, mul_comm (dt _), mul_comm (dt _), h1, h2, map_one, div_one]

theorem isSdLat_of {L : Submodule (𝓞 E) (Sp E n)} (h : IsSDLat E n L) : IsSdLat L := by
  refine ⟨Submodule.IsLattice.of_fg E h.1, ?_⟩
  ext x
  rw [mem_dual, h.2.2]
  refine forall₂_congr fun y _ => ?_
  rw [Submodule.mem_one]
  rfl

end General

theorem detId_normOne_mul (D : D7) (n : ℕ) (L L' L'' : Submodule (𝓞 D.host.E) (Fin n → D.host.E))
    (hL : StandardLatticesGL3.SD D L) (hL' : StandardLatticesGL3.SD D L') (hL'' : StandardLatticesGL3.SD D L'') :
    TaylorLogMetric.N1 D (TaylorLogMetric.detId D L L') ∧ TaylorLogMetric.detId D L L'' = TaylorLogMetric.detId D L L' * TaylorLogMetric.detId D L' L'' := by
  letI := D.host.cmStar
  have hs : ∀ x : D.host.E, star x = D.host.conj x := bridge_star_holds D.R D.host
  have hfull {N : Submodule (𝓞 D.host.E) (Fin n → D.host.E)} (h : IsSDLat D.host.E n N) :
      Submodule.IsFullLattice D.host.E N :=
    { toIsLattice := Submodule.IsLattice.of_fg _ h.1
      span_eq_top := h.2.1 }
  refine ⟨?_, relDet_mul (hfull hL) (hfull hL') (hfull hL'')⟩
  obtain ⟨J, hJ, e⟩ := normOne_relDet (isSdLat_of hL) (isSdLat_of hL')
  exact ⟨J, fun x => by rw [hJ, hs]; rfl, e⟩

end GlobalTheory.RelDetIdeal
end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions NumberField

namespace GlobalTheory.PerRedU

theorem perTwAt_of_perDecTw {D : D7} {Dx : DivX D} {T : TwForms D} (hD : DGamDef D) {u : D.what₂.Word} {μ : D.what₂.Tup}
    (h : Formalism.MainNotions.RT.PeriodPointConditions.PerDecTw D Dx T u μ) :
    ∀ x ∈ (T.fm u μ).ptLat.L, ∀ F ∈ (D.what₂.Mtilde μ).carrier, F ∈ D.what₂.V0 μ →
      ∃ y : D.what₂.LL, D.what₂.embLL y = (D.PTw u μ).period ((T.fm u μ).ptEmb x) ((D.eMtTw u μ).symm F) ∧
        ∀ w : D.what₂.places.Pl, D.what₂.places.resChar w ∉ Dx.Qp μ →
          y = 0 ∨ -ur D w (Formalism.MainNotions.WeilJacquetShalikaLaw.vDG D u w) ≤ (vAdd (D.plEq w) y : ℝ) := by
  intro x hx F hF _
  obtain ⟨pc, hs, hi⟩ := h
  choose y hy hv using hi x hx F hF
  refine ⟨∑ c, ((Nat.card ((T.fm u μ).stabilizer₂ c) : ℕ) : D.what₂.LL)⁻¹ * y c, ?_, fun w hw => ?_⟩

  · rw [hs, map_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [map_mul, map_inv₀, map_natCast, hy c]
  · refine Finset.sum_induction _ (fun t => t = 0 ∨ -ur D w (Formalism.MainNotions.WeilJacquetShalikaLaw.vDG D u w) ≤ (vAdd (D.plEq w) t : ℝ))
      (fun a b ha hb => Formalism.MainNotions.WeightDegreeSizes.pair_add_ge D w ha hb) (Or.inl rfl) fun c _ => ?_
    rcases hv c w hw with h0 | h0
    · left; rw [h0, mul_zero]
    by_cases hy0 : y c = 0
    · left; rw [hy0, mul_zero]
    right
    have hn0 : ((Nat.card ((T.fm u μ).stabilizer₂ c) : ℕ) : D.what₂.LL) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
    rw [Formalism.MainNotions.OrbitPlaces.vAdd_mul w (inv_ne_zero hn0) hy0, Formalism.MainNotions.OrbitPlaces.vAdd_inv w hn0]
    have hb := Formalism.MainNotions.DIV.HookProducts.AdmPerTw.vAdd_dvd_le (D := D) w (D.mem u).C.DGam_pos.ne'
      (Formalism.MainNotions.DIV.HookProducts.AdmPerTw.card_stabilizer_dvd₂ hD T u μ c)
    have h0' : (0 : ℝ) ≤ (vAdd (D.plEq w) (y c) : ℝ) := by exact_mod_cast h0
    unfold Formalism.MainNotions.WeilJacquetShalikaLaw.vDG
    push_cast
    linarith

theorem exists_muAt_of_usedT {D : D7} {μ : D.what₂.Tup} (hU : Formalism.MainNotions.LocalQuadraticParts.UsedT D μ) (hμ : μ ≠ D.what₂.mu0) :
    ∃ w, μ = D.what₂.muAt w :=
  hU.resolve_left hμ

theorem admissiblePeriodTwists_of_periodDecompositions {D : D7} {Dx : DivX D} {T : TwForms D}
    (h : ∀ u μ, μ ≠ D.what₂.mu0 → (∃ w, μ = D.what₂.muAt w) → Formalism.MainNotions.RT.PeriodPointConditions.PerDecTw D Dx T u μ) :
    Formalism.L2.G.Adm2InU.TwistedPeriodAdmissible D Dx T :=
  fun hD u μ hU hμ => perTwAt_of_perDecTw hD (h u μ hμ (exists_muAt_of_usedT hU hμ))

theorem main : ∀ (D : D7) (Dx : DivX D) (T : TwForms D), (∀ u μ, μ ≠ D.what₂.mu0 → (∃ w, μ = D.what₂.muAt w) → Formalism.MainNotions.RT.PeriodPointConditions.PerDecTw D Dx T u μ) → Formalism.L2.G.Adm2InU.TwistedPeriodAdmissible D Dx T :=
  fun _ _ _ h => admissiblePeriodTwists_of_periodDecompositions h

end GlobalTheory.PerRedU

end
end
