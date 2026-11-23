module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.MemHalfCosetSelf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1747
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1781
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumOKEx
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationLeOneOfMem
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PadOneMemSecondBlockTriangular
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1195
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2136
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1374
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2523
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1871
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsNotRelZero
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BlkGLMem
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ComplexEmbeddingHermitianQuadrupleSum
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2393
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2510
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.Bundle001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2521
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2467
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1970
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1522
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2281
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1945
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2287
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2518
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2520
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2468
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2471
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2469
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle269
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle270
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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Divisors.TupleReadBaseTupleEqFamily
import Development.AbelianVarietyTheory.Definitions.Divisors.TwistedPlaceChoiceLiesOverPair
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1103

@[expose] public section

section

open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.BigTop GlobalTheory.BigTop.Fun

noncomputable section

namespace GlobalTheory.PhaseField

open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.SplitFlip GlobalTheory.SplitWeil ValuativeRel MeasureTheory

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

theorem exists_field_roots {n : ℕ} (hn : 0 < n) : ∃ M : IntermediateField ℚ ℂ, FiniteDimensional ℚ M ∧
    ∀ z : ℂ, z ^ n = 1 → z ∈ Set.range (algebraMap M ℂ) := by
  classical
  set S : Set ℂ := {z | z ^ n = 1} with hSdef
  have hS : S = ((Polynomial.nthRoots n (1 : ℂ)).toFinset : Set ℂ) := by
    ext z; simp [S, Polynomial.mem_nthRoots hn]
  haveI : Finite S := by rw [hS]; infer_instance
  have hint : ∀ z ∈ S, IsIntegral ℚ z := fun z hz =>
    ⟨Polynomial.X ^ n - Polynomial.C 1, Polynomial.monic_X_pow_sub_C _ hn.ne', by
      simp [Polynomial.eval₂_sub, show z ^ n = 1 from hz]⟩
  exact ⟨IntermediateField.adjoin ℚ S, IntermediateField.finiteDimensional_adjoin hint,
    fun z hz => ⟨⟨z, IntermediateField.subset_adjoin ℚ S hz⟩, rfl⟩⟩

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem val_resCard_le {ϖ : kˣ} (hϖ : IsUnif ϖ) : valuation k ((Nat.card 𝓀[k] : ℕ) : k) ≤ valuation k (ϖ : k) := by
  classical
  letI := Fintype.ofFinite 𝓀[k]
  have h0 : IsLocalRing.residue 𝒪[k] ((Nat.card 𝓀[k] : ℕ) : 𝒪[k]) = 0 := by
    rw [map_natCast, Nat.card_eq_fintype_card]
    exact FiniteField.cast_card_eq_zero _
  have hmem : ((Nat.card 𝓀[k] : ℕ) : 𝒪[k]) ∈ IsLocalRing.maximalIdeal 𝒪[k] :=
    (IsLocalRing.residue_eq_zero_iff _).1 h0
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, Valuation.Integer.not_isUnit_iff_valuation_lt_one] at hmem
  rw [hϖ, le_uniformizer_iff]
  simpa using hmem

theorem exists_pow_eq_one_of_le {ψ : AddChar k Circle} {ϖ : kˣ} (hψ : HasConductor ψ 1) (hϖ : IsUnif ϖ) (N : ℕ) :
    ∃ n : ℕ, 0 < n ∧ ∀ z : k, valuation k z ≤ valuation k (((ϖ ^ N)⁻¹ : kˣ) : k) → ((ψ z : Circle) : ℂ) ^ n = 1 := by
  have hq : 0 < Nat.card 𝓀[k] := Nat.card_pos
  refine ⟨Nat.card 𝓀[k] ^ N, pow_pos hq N, fun z hz => ?_⟩
  have h1 : valuation k (((Nat.card 𝓀[k] ^ N : ℕ) : k) * z) ≤ 1 := by
    rw [map_mul, Nat.cast_pow, map_pow]
    calc valuation k ((Nat.card 𝓀[k] : ℕ) : k) ^ N * valuation k z
        ≤ valuation k (ϖ : k) ^ N * valuation k (((ϖ ^ N)⁻¹ : kˣ) : k) :=
          mul_le_mul' (pow_le_pow_left₀ zero_le' (val_resCard_le hϖ) N) hz
      _ = 1 := by
          rw [Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val, map_inv₀, map_pow]
          exact mul_inv_cancel₀ (pow_ne_zero _ (by simp))
  have h2 : ψ (((Nat.card 𝓀[k] ^ N : ℕ) : k) * z) = 1 :=
    (hψ 1).2 le_rfl _ (by simpa using h1)
  rw [← nsmul_eq_mul, AddChar.map_nsmul_eq_pow] at h2
  rw [← Circle.coe_pow, h2, Circle.coe_one]

end Local


open GlobalTheory.RootEx Matrix in
theorem phase_bounded {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [MeasurableSpace k] [BorelSpace k] (G : Grid k) (hs : 1 ≤ G.s) (ψ : AddChar k Circle) (ν : Measure k)
    [ν.IsAddHaarMeasure] (ϖ : kˣ) (e : ℕ) (T : G.Args → ℂ) (keep : Bool) (g : G.VertexGroup) (hm : 2 ≤ G.m)
    (hϖ : IsUnif ϖ) (hψ : HasConductor ψ 1) (hT : G.IsTensor ϖ e (oppositePath G.m) T) :
    ∃ N : ℕ, ∀ (x : ColArgs G) (y : RowArgs G) (v : Vars G), flatTensor hs ψ ν (moved G keep g T) x y ≠ 0 →
      moved G keep g T (fill hs x y v) ≠ 0 → valuation k (phase x v) ≤ valuation k (((ϖ ^ N)⁻¹ : kˣ) : k) := by
  classical
  obtain ⟨n1, hsupp⟩ := FlatSupp.flatTensor_support G hs ψ ν ϖ e T keep g hϖ hT
  obtain ⟨n2, hlast⟩ := FlatLast.flatTensor_lastRow_bounded G hs ψ ν ϖ e T keep g hm hϖ hψ hT
  choose N hN using fun b : Edge =>
    FlatSupp.exists_bound_conj hϖ (Assignment.one.read (g b.tgt)) (Assignment.one.read (g b.src))
  set K := max n1 (max n2 ((oppositePath G.m).toFinset.sup N)) with hK
  set c := valuation k (((ϖ ^ K)⁻¹ : kˣ) : k) with hc
  have hc1 : 1 ≤ c := by
    have := FlatSupp.val_inv_pow_mono hϖ (Nat.zero_le K)
    rwa [show valuation k (((ϖ ^ 0)⁻¹ : kˣ) : k) = 1 by simp] at this
  have hcc : valuation k (((ϖ ^ (K + K))⁻¹ : kˣ) : k) = c * c := by
    rw [hc, FlatSupp.val_inv_pow, FlatSupp.val_inv_pow, pow_add, mul_inv]
  refine ⟨K + K, fun x y v hF hM => ?_⟩
  rw [hcc]
  have hT0 : T (G.moveArgs .one g (fill hs x y v)) ≠ 0 := by
    intro h0
    apply hM
    simp [moved, Grid.pathAct, h0]
  have key : ∀ b ∈ oppositePath G.m, ∀ r s, valuation k (fill hs x y v b r s) ≤ c := by
    intro b hb r s
    refine le_trans (hN b _ (fun r s => ?_) r s) (FlatSupp.val_inv_pow_mono hϖ
      ((Finset.le_sup (f := N) (List.mem_toFinset.2 hb)).trans ((le_max_right _ _).trans (le_max_right _ _))))
    have hm' : (G.moveArgs .one g (fill hs x y v)) b ∈ matLat _ (GlobalTheory.SplitFlip.stdLat k _) := by
      by_contra h
      exact hT0 (hT.2.1 _ b hb h)
    exact mem_matLat_stdLat.1 hm' r s
  have hstep : ∀ (j : Fin (G.m - 1)) p q, valuation k (stepPt (x j) (v j) p q) ≤ c := by
    intro j p q
    have hmem : Edge.theta G.m j ∈ oppositePath G.m := by simp [oppositePath]; omega
    have hj' : (j : ℕ) < G.m - 1 := j.2
    have h := key _ hmem
      (frame (a := topRank G j) (b := G.rank (G.m, j)) (c := G.m - 2 - j + 1) (by have := topRank_add hs j; omega) q)
      (frame (a := topRank G (j + 1)) (b := G.rank (G.m, j + 1)) (c := G.m - 2 - j)
        (by have := topRank_add hs (j + 1); omega) p)
    rw [fill_theta, transpose_apply, downMap, dite_eq_left hj'] at h
    simpa [reindex_apply, submatrix_apply, Equiv.symm_apply_apply] using h
  have hx : ∀ j, j < G.m → ∀ r s, valuation k (x j r s) ≤ c := by
    intro j hj r s
    by_cases hr : j + 1 = G.m ∧ r = topLast G (j + 1)
    · obtain ⟨h1, rfl⟩ := hr
      obtain rfl : j = G.m - 1 := by omega
      exact (hlast x y hF s).trans (FlatSupp.val_inv_pow_mono hϖ ((le_max_left _ _).trans (le_max_right _ _)))
    · exact ((hsupp x y hF).1 j hj r s fun h h' => hr ⟨h, h'⟩).trans (FlatSupp.val_inv_pow_mono hϖ (le_max_left _ _))
  have hcol : ∀ j r, valuation k (colVar x v j r) ≤ c := fun j r => hstep j _ _
  have hrow : ∀ (j : Fin (G.m - 1)) r, valuation k (rowVar x v (j + 1) r) ≤ c := by
    intro j r
    unfold rowVar
    split_ifs with h
    · refine Valuation.map_sum_le _ fun l _ => ?_
      split_ifs
      · exact hstep ⟨_, h⟩ _ _
      · simp
    · exact hx _ (by omega) _ _
  have hch : ∀ j : Fin (G.m - 1), valuation k (ch (stepPt (x j) (v j))) ≤ c := fun j =>
    Valuation.map_sum_le _ fun i _ => hstep j _ _
  unfold phase
  refine Valuation.map_sum_le _ fun j _ => ?_
  refine Valuation.map_add_le _ ((hch j).trans (le_mul_of_one_le_right' hc1)) ?_
  split_ifs
  · refine Valuation.map_sum_le _ fun r _ => ?_
    rw [map_mul]
    exact mul_le_mul' (hrow j r) (hcol j r)
  · simp

theorem phases_core {D : D7} {T : Type} [Finite T] {L : LevCh D T} {sc : Consts} {μ₀ : T} (hL : L.Is μ₀) {G : GridData L sc}
    {W : G.Weil} {U : Set T} (S : GridChoice W U) (hde : Nat.Coprime D.host.pde (D.host.QS * D.host.q) ∧ Nat.Coprime D.host.pde' (D.host.QS * D.host.q))
    (hc : ∀ t, ∀ P ∈ L.Q t, ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal) :
    ∃ M : IntermediateField ℚ ℂ, FiniteDimensional ℚ M ∧ ∀ t Φ, ∀ β ∈ S.supp t Φ, PhasesIn (algebraMap M ℂ) S t Φ β := by
  classical
  have hm : 2 ≤ D.R.m := D.R.two_le_m
  have hloc : ∀ t Φ (β : CosFam G t) (w : locPl G t), ∃ n : ℕ, 0 < n ∧ ∀ x y e, (S.term t Φ β w).datum x y ≠ 0 →
      moved (locGrid G t w) (keepAt G w) ((repsAt G t w).elt (β w)) (Tflip W S.B t Φ w) (fill one_le_sLen x y e) ≠ 0 →
      ((psiAt W w.1 (phase x e) : Circle) : ℂ) ^ n = 1 := by
    intro t Φ β w
    have hg := (Good.locGrid_isGood hL G W t hde (hc t)).1 w.1 w.2
    have h00 := hg.square 0 (by change 0 < D.R.m; omega) 0 (by change 0 < D.R.m; omega)
    haveI := (isUnitVol_unitVol w.1).1
    obtain ⟨N, hN⟩ := phase_bounded (locGrid G t w.1) one_le_sLen (psiAt W w.1) (unitVol w.1) (unifAt w.1) (depthAt G w.1)
      (Tflip W S.B t Φ w.1) (keepAt G w.1) ((repsAt G t w.1).elt (β w)) hm h00.unif h00.cond
      (isTensor_Tflip hL W S.B t Φ hde (hc t) w.2)
    obtain ⟨n, hn, hpow⟩ := exists_pow_eq_one_of_le h00.cond h00.unif N
    exact ⟨n, hn, fun x y e h1 h2 => hpow _ (hN x y e h1 h2)⟩
  choose nf hnf hpow using hloc
  haveI : ∀ t Φ, Finite (S.supp t Φ) := fun t Φ => ((S.sumOK_flat_fin_ex hL t Φ hde (hc t)).2.1).to_subtype
  haveI : Finite G.Datum := G.finite_datum (GlobalTheory.DiagLiftFix.isLattice_of_isFrame (hL.βY 0 (by omega)).choose_spec.1).fg
  letI : Fintype (Σ t : T, Σ Φ : G.Datum, (S.supp t Φ) × locPl G t) := Fintype.ofFinite _
  set n := ∏ i : (Σ t : T, Σ Φ : G.Datum, (S.supp t Φ) × locPl G t), nf i.1 i.2.1 i.2.2.1.1 i.2.2.2 with hn
  have hn0 : 0 < n := Finset.prod_pos fun i _ => hnf _ _ _ _
  obtain ⟨M, hM, hMr⟩ := exists_field_roots hn0
  refine ⟨M, hM, fun t Φ β hβ w x y e h1 h2 => hMr _ ?_⟩
  obtain ⟨c, hc'⟩ : nf t Φ β w ∣ n :=
    Finset.dvd_prod_of_mem (fun i : (Σ t : T, Σ Φ : G.Datum, (S.supp t Φ) × locPl G t) => nf i.1 i.2.1 i.2.2.1.1 i.2.2.2)
      (Finset.mem_univ ⟨t, Φ, ⟨β, hβ⟩, w⟩)
  rw [hc', pow_mul, hpow t Φ β w x y e h1 h2, one_pow]

end GlobalTheory.PhaseField

namespace GlobalTheory.BigTop.Fun

end GlobalTheory.BigTop.Fun
end
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

namespace GlobalTheory.InertSph

theorem vacV_fixed : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → v ∉ X.T →
    ∀ k ∈ GlobalTheory.InertSph.KAt σ G.V v, Acts (evFin F v) (om (k, 1)) (G.M.vac v) (G.M.vac v) := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT v w hin hvT k hk
  obtain ⟨hSB, hne, θ, hθ, hfix⟩ := hT.geo.hM.vac v
  obtain ⟨φ₁, hφ₁, hact⟩ := GlobalTheory.T.weilRepresentationLocality_unitaryGroupV_pairVW F E σ B a a' G X om om' hT v k hk.1 _ hSB
  have hfix₁ := GlobalTheory.T.weilOperator_latticeStabiliser_left_preserves_vacuumType F E σ B a a' G X om om' hT v k hk θ hθ _ hSB φ₁ hφ₁ hfix hact
  obtain ⟨c, rfl⟩ := GlobalTheory.T.heisenbergSelfDualLattice_fixedFunctions_line F E σ B a a' G X om om' hT v (hT.base.inert v w hin).2.2
    (GlobalTheory.T.tensorLattice_inertPlace_selfDual F E σ B a a' G X om om' hT v w hin) θ hθ _ hSB hne hfix φ₁ hφ₁ hfix₁
  have hc := GlobalTheory.T.latticeStabiliser_vacuum_eigenvalue_one_inert_place F E σ B a a' G X om om' hT v w hin hvT k hk c hact
  rw [hc, one_smul] at hact
  exact hact

theorem vac_fixed_pair : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → v ∉ X.T →
    ∀ k ∈ GlobalTheory.InertSph.KAt σ G.V v, ∀ k' ∈ GlobalTheory.InertSph.KAt σ G.W v,
      Acts (evFin F v) (om (k, k')) (G.M.vac v) (G.M.vac v) := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT v w hin hvT k hk k' hk' r hr
  have h1 := vacV_fixed F E σ B a a' G X om om' hT v w hin hvT k hk
  have h2 := GlobalTheory.T.inert_place_lattice_stabiliser_fixes_vacuum F E σ B a a' G X om om' hT v w hin hvT k' hk'
  have e : om (k, k') = om (k, 1) * om (1, k') := by
    rw [← map_mul, Prod.mk_mul_mk, mul_one, one_mul]
  rw [e, Module.End.mul_apply, h2 r hr, h1 r hr]

end GlobalTheory.InertSph
end

section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Classical

theorem _root_.GlobalTheory.T.continuous_weilDatum_transport_cm_apply : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (χS χT : (AF F ⊗[F] E)ˣ →* Circle), Formalism.IndefR.DatumF.IsHeckeCharF χS → Formalism.IndefR.DatumF.IsHeckeCharF χT →
        Formalism.IndefR.DatumF.ResEtaF χS nS → Formalism.IndefR.DatumF.ResEtaF χT nT →
        ∀ ω : Formalism.IndefR.DatumF.GAF σ JS × Formalism.IndefR.DatumF.GAF σ JT →* Module.End ℂ (Formalism.IndefR.DatumF.WOF F E nS nT → ℂ),
        Formalism.IndefR.DatumF.IsWeilDatumOF σ JS JT (fun w : InfinitePlace F => (B.emb w).1) ξ₀ B.ψ χS χT ω →
        ∀ (JA : Matrix (Fin nT) (Fin nT) E) (JB : Matrix (Fin nS) (Fin nS) E) (ξ : AF F ⊗[F] E), JA = JTᵀ →
          ξ • incM F JB = incM F (ξ₀ • JS⁻¹) →
          ∀ (κ : Type) [Fintype κ] (co : Darboux (symp (cA σ) ξ (incM F JA) (incM F JB)) κ),
            (∀ x : Matrix (Fin nT) (Fin nS) E, ∃ y z : κ → F,
              co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
            ∀ om : UG (cA σ) (incM F JA) × UG (cA σ) (incM F JB) →* Module.End ℂ ((κ → AF F) → ℂ),
              GlobalTheory.WeilSchrodinger.IsTransportF σ B.ψ co ω om → ∀ Φ ∈ schA F κ, ∀ z : κ → AF F, Continuous fun p => om p Φ z := by
  first | exact @GlobalTheory.WeilContF.continuous_transportF_apply | exact GlobalTheory.WeilContF.continuous_transportF_apply | (intros; apply GlobalTheory.WeilContF.continuous_transportF_apply <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.BigRouteIdent

open GlobalTheory.RouteSeesaw

theorem kerBig_norm_le_thetaKO : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (hL : L.Is μ₀)
    (W : G.Weil) (B : Frames G) (ρ : RealMatch W) (t : T) (i j : Fin D.R.m) (hT : SquareTriple W t i j)
    (M : Vol G) (hM : M.Is t) (Θ : TotT G (routeBig t i j)) (Θ' : TotT G (routeSmall t i j)) (hΘ : IsMatched B t ρ i j Θ Θ') (g₁ : GA D (G.V (.grid (i + 1) j))),
    ∃ (ε : Bool) (ω : GlobalTheory.Grid.WRep (G.V (.grid (i + 1) (j + 1))) (GlobalTheory.Doubling.hsum (G.V (.grid i (j + 1))) (G.V (.grid (i + 1) j))))
      (χ χ' : (AE D)ˣ →* Circle) (Φ : WO (G.V (.grid (i + 1) (j + 1))) (GlobalTheory.Doubling.hsum (G.V (.grid i (j + 1))) (G.V (.grid (i + 1) j))) → ℂ) (C₀ : ℝ),
      GlobalTheory.Grid.IsWeil W.ψ ε _ _ χ χ' ω ∧ IsThetaFunO W.ψ (GlobalTheory.Grid.sgn ε (G.V (.grid (i + 1) (j + 1)))) _ Φ ∧
      ∀ g u, ‖kerBig W Θ g g₁ u‖ ≤ C₀ * ‖thetaKO ω u (GlobalTheory.SquareComm.blk _ _ (g, g₁)) Φ‖ := by
  intro D T L sc G μ₀ hL W B ρ t i j hT M hM Θ Θ' hΘ g₁
  have hd := GlobalTheory.T.isThetaFunO_of_matchedSquare_bigRoute hL W B ρ t i j Θ Θ' hΘ
  have h1 := W.om_is (.chi i (j + 1)) (show (↑i + 1 ≤ D.R.m ∧ ↑j + 1 ≤ D.R.m) by omega)
  have h2 := W.om_is (.mu t (i + 1) j) (show (↑i + 1 ≤ D.R.m ∧ ↑j + 1 ≤ D.R.m) by omega)
  obtain ⟨ω₂, χa, χb, hω₂, hadj⟩ := GlobalTheory.T.weilDatum_adjoint_negSource_kernels_agree W.ψ W.ψ_std _ _ _ _ _ h2
  obtain ⟨ω', χ, χ', c, hω', hc, hbox⟩ := GlobalTheory.SeesawSumTarget.seesaw_sum W.ψ W.ψ_std _ _ _ _ _ _ _ _ ω₂ h1 hω₂
  let S := G.V (.grid (↑i + 1) (↑j + 1))
  let A := G.V (.grid (↑i) (↑j + 1))
  let Bs := G.V (.grid (↑i + 1) ↑j)
  let Φ : WO (negSp S) (GlobalTheory.Doubling.hsum A Bs) → ℂ :=
    Θ.sum fun d a => a • box2 (S := negSp S) (A := A) (B := Bs) d.1.2 (fun y => d.2 (adjM S Bs y))
  have hth : ∀ d ∈ Θ.support, IsThetaFunO W.ψ (negSp S) (GlobalTheory.Doubling.hsum A Bs)
      (box2 (S := negSp S) (A := A) (B := Bs) d.1.2 (fun y => d.2 (adjM S Bs y))) := fun d hdm =>
    (hbox _ _ (hd d hdm).1 ((hadj _ (hd d hdm).2).1)).1
  have e : ∀ u g, ∀ d ∈ Θ.support, thetaKO ω' (negGA S u) (GlobalTheory.SquareComm.blk A Bs (g, g₁))
      (box2 (S := negSp S) (A := A) (B := Bs) d.1.2 (fun y => d.2 (adjM S Bs y))) =
      c (negGA S u) g g₁ * (W.kerA (.right i (j + 1)) d.1.2 g u * W.kerA (.down t (i + 1) j) d.2 u g₁) := fun u g d hdm => by
    rw [(hbox _ _ (hd d hdm).1 ((hadj _ (hd d hdm).2).1)).2, (hadj _ (hd d hdm).2).2]
    rfl
  refine ⟨true, ω'.comp ((negGA S).toMonoidHom.prodMap (MonoidHom.id _)), χ, χ', Φ, 1, hω', ?_, ?_⟩
  · let U : Submodule ℂ (WO (negSp S) (GlobalTheory.Doubling.hsum A Bs) → ℂ) :=
      { carrier := {g | IsThetaFunO W.ψ (negSp S) (GlobalTheory.Doubling.hsum A Bs) g}
        add_mem' := fun ha hb => GlobalTheory.OrientedHeis.theta_add ha hb
        zero_mem' := GlobalTheory.OrientedHeis.theta_zero
        smul_mem' := fun c _ hg => GlobalTheory.OrientedHeis.theta_smul c hg }
    show Φ ∈ U
    exact U.sum_mem fun d hdm => U.smul_mem _ (hth d hdm)
  · intro g u
    have key : ω' (negGA S u, GlobalTheory.SquareComm.blk A Bs (g, g₁)) Φ 0 = c (negGA S u) g g₁ * kerBig W Θ g g₁ u := by

      simp only [Φ, kerBig, Finsupp.sum, map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun d hdm => ?_
      have := e u g d hdm
      simp only [thetaKO] at this
      rw [this]; ring
    refine le_of_eq ?_
    show ‖kerBig W Θ g g₁ u‖ = 1 * ‖ω' (negGA S u, GlobalTheory.SquareComm.blk A Bs (g, g₁)) Φ 0‖
    rw [key, norm_mul, hc, one_mul, one_mul]

end GlobalTheory.BigRouteIdent

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.Grid

noncomputable section

namespace GlobalTheory.FunObj

theorem routeBig_kerBig_integrableOn : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (hWC : GlobalTheory.SquareSt.WeilConvergence) {μ₀ : T} (hL : L.Is μ₀)
    (W : G.Weil) (B : Frames G) (ρ : RealMatch W) (t : T) (i j : Fin D.R.m) (hT : SquareTriple W t i j)
    (M : Vol G) (hM : M.Is t) (Θ : TotT G (routeBig t i j)) (Θ' : TotT G (routeSmall t i j)) (hΘ : IsMatched B t ρ i j Θ Θ') (g₁ : GA D (G.V (.grid (i + 1) j))),
    ∀ g : GA D (G.V (.grid i (j + 1))), IntegrableOn (kerBig W Θ g g₁) (M.fd (.grid (i + 1) (j + 1))) (M.ν (.grid (i + 1) (j + 1))) := by
  intro D T L sc G hWC μ₀ hL W B ρ t i j hT M hM Θ Θ' hΘ g₁ g
  have hHF : GlobalTheory.SquareComm.IsHaarFD _ (M.ν (.grid (i + 1) (j + 1))) (M.fd (.grid (i + 1) (j + 1))) :=
    (hM.vtx (.grid (i + 1) (j + 1)) ⟨i.2, j.2⟩).haar_fund
  obtain ⟨p, hsig, hrk⟩ := GlobalTheory.T.squareThetaTriple_exists_signature_rank_add_lt W t i j hT M hM
  have key : ∀ d ∈ Θ.support, Integrable (fun u => Θ d * (W.kerA (.right i (j + 1)) d.1.2 g u *
      W.kerA (.down t (i + 1) j) d.2 u g₁)) ((M.ν (.grid (i + 1) (j + 1))).restrict (M.fd (.grid (i + 1) (j + 1)))) := by
    intro d hd
    obtain ⟨ε, X, χ, χ', ω, hω, hX, Φ, hΦ, h, c, he⟩ := GlobalTheory.T.routeBigVertex_kernelProduct_eq_const_mul_thetaKernel hL W B ρ t i j hT M hM Θ Θ' hΘ d hd g g₁
    obtain ⟨N, C, hmi⟩ := hWC D W.ψ W.θ W.θ_is ε _ X χ χ' ω hω p hsig (hX ▸ hrk) _ _ hHF Φ hΦ
    refine Integrable.const_mul ?_ _
    simp_rw [he]
    exact ((hmi h).1).const_mul c
  have e : kerBig W Θ g g₁ = fun u => ∑ d ∈ Θ.support, Θ d * (W.kerA (.right i (j + 1)) d.1.2 g u *
      W.kerA (.down t (i + 1) j) d.2 u g₁) := by
    funext u; rfl
  rw [IntegrableOn, e]
  exact integrable_finsetSum _ key

end GlobalTheory.FunObj

end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift

namespace GlobalTheory.PDForm.LiftNat



theorem main : (∀ (D D' : Data) (Λ : Lift D) (Λ' : Lift D') (σ : D.R →+* D'.R) (φ : D'.X ⟶ D.X) (φ₀ : D'.X₀ ⟶ D.X₀) (hφ : φ ≫ D.s = D'.s ≫ spMap σ) (m : IsMor D.κ D.t D'.κ D'.t σ φ₀), φ₀ ≫ D.i = D'.i ≫ φ → ∀ c h h', Λ.Rel1 c h → Λ'.Rel1 (m.pull1 c) h' → IsPull1 hφ h h') ∧ ∀ (D D' : Data) (Λ : Lift D) (Λ' : Lift D') (σ : D.R →+* D'.R) (φ : D'.X ⟶ D.X) (φ₀ : D'.X₀ ⟶ D.X₀) (hφ : φ ≫ D.s = D'.s ≫ spMap σ) (m : IsMor D.κ D.t D'.κ D'.t σ φ₀), φ₀ ≫ D.i = D'.i ≫ φ → ∀ c h h', Λ.Rel2 c h → Λ'.Rel2 (m.pull2 c) h' → IsPull2 hφ h h' := by
  refine ⟨?_, ?_⟩
  · intro D D' Λ Λ' σ φ φ₀ hφ m hi c h h' ⟨k, f, w, hc, hh, hk, hw⟩ ⟨k', f', w', hc', hh', hk', hw'⟩
    subst hh hh'
    obtain ⟨g0, hg0⟩ := GlobalTheory.T.compatibleFormsCocycles_degreeOne_differ_coboundary _ _ _ _ _ _ _ _ _ _ _ _ m k k' f f' hk hk' (by rw [hc', ← hc])
    obtain ⟨θ, hθ⟩ := GlobalTheory.T.exists_natTrans_lifts_over_affine_pairs D D' Λ Λ' σ φ φ₀ hφ m hi
    have e1 : (morMap m).h1 (QuotientAddGroup.mk k) = QuotientAddGroup.mk k' := by
      change (QuotientAddGroup.mk ((morMap m).z1 k) : (KK D'.κ D'.t).H1) = QuotientAddGroup.mk k'
      rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf]
      refine ⟨-g0, ?_⟩
      rw [map_neg, hg0]
      change -((morMap m).p1 k.1 - k'.1) = -((morMap m).p1 k.1) + k'.1
      abel
    have e2 : ((pairB Λ' φ m).pre θ).h1 (QuotientAddGroup.mk k) =
        ((KK D'.κ D'.t).resMap (pairFst φ ⋙ Λ'.L)).h1 (QuotientAddGroup.mk k') := by
      rw [(GlobalTheory.CxCoh.joinedOne_inst.2.1 _ _ θ (CxMap.joined_pre _ θ)).2, pairB, CxMap.cohomOne_pullback_comp, e1]
    change (QuotientAddGroup.mk (((pairB Λ' φ m).pre θ).z1 k) : ((KK D'.κ D'.t).res (pairFst φ ⋙ Λ'.L)).H1) =
      QuotientAddGroup.mk (((KK D'.κ D'.t).resMap (pairFst φ ⋙ Λ'.L)).z1 k') at e2
    rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf] at e2
    obtain ⟨g, hg⟩ := e2
    refine GlobalTheory.T.deRham_degree_one_class_pullback_of_coboundary D D' Λ Λ' σ φ φ₀ hφ m θ hθ k k' w w' hw hw' (-g) ?_
    rw [map_neg, hg]
    change -(-(((pairB Λ' φ m).pre θ).p1 k.1) + ((KK D'.κ D'.t).resMap (pairFst φ ⋙ Λ'.L)).p1 k'.1) = _
    abel
  · intro D D' Λ Λ' σ φ φ₀ hφ m hi c h h' hr hr'
    obtain ⟨k, f, w, hc, hh, hk, hw⟩ := hr
    obtain ⟨k', f', w', hc', hh', hk', hw'⟩ := hr'
    subst hh hh'
    obtain ⟨g0, hg0⟩ := GlobalTheory.T.compatibleFormsCocycles_degreeTwo_differ_coboundary _ _ _ _ _ _ _ _ _ _ _ _ m k k' f f' hk hk' (by rw [hc', ← hc])
    obtain ⟨θ, hθ⟩ := GlobalTheory.T.exists_natTrans_lifts_over_affine_pairs D D' Λ Λ' σ φ φ₀ hφ m hi
    have e1 : (morMap m).h2 (QuotientAddGroup.mk k) = QuotientAddGroup.mk k' := by
      change (QuotientAddGroup.mk ((morMap m).z2 k) : (KK D'.κ D'.t).H2) = QuotientAddGroup.mk k'
      rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf]
      refine ⟨-g0, ?_⟩
      rw [map_neg, hg0]
      change -((morMap m).p2 k.1 - k'.1) = -((morMap m).p2 k.1) + k'.1
      abel
    have e2 : ((pairB Λ' φ m).pre θ).h2 (QuotientAddGroup.mk k) =
        ((KK D'.κ D'.t).resMap (pairFst φ ⋙ Λ'.L)).h2 (QuotientAddGroup.mk k') := by
      have j := GlobalTheory.CxCoh.JoinedTwoProof.main ((pairB Λ' φ m).pre θ) (pairB Λ' φ m) θ (CxMap.joined_pre _ θ)
        (QuotientAddGroup.mk k)
      refine j.trans ?_
      have j2 := CxMap.cohomTwo_pullback_comp (morMap m) ((KK D'.κ D'.t).resMap (pairFst φ ⋙ Λ'.L)) (QuotientAddGroup.mk k)
      refine j2.trans ?_
      exact congrArg _ e1
    change (QuotientAddGroup.mk (((pairB Λ' φ m).pre θ).z2 k) : ((KK D'.κ D'.t).res (pairFst φ ⋙ Λ'.L)).H2) =
      QuotientAddGroup.mk (((KK D'.κ D'.t).resMap (pairFst φ ⋙ Λ'.L)).z2 k') at e2
    rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf] at e2
    obtain ⟨g, hg⟩ := e2
    refine GlobalTheory.T.deRham_degree_two_class_pullback_of_coboundary D D' Λ Λ' σ φ φ₀ hφ m θ hθ k k' w w' hw hw' (-g) ?_
    rw [map_neg, hg]
    change -(-(((pairB Λ' φ m).pre θ).p2 k.1) + ((KK D'.κ D'.t).resMap (pairFst φ ⋙ Λ'.L)).p2 k'.1) = _
    abel

end GlobalTheory.PDForm.LiftNat
end
end
