module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle049
public import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle065
public import Formalism.LocalRingCardinality.Bundle002
public import Formalism.LocalRingCardinality.DataCD
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle016
public import Formalism.SharpRestriction.LevelLetterCocycles.DataN
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.RingTheory.EssentialFiniteness
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle064
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle063
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle062
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Formalism.ConjugateSelfDual.Bundle001
import ReciprocityTheory.GaloisValuations.GlobalA
import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.HCFFromRecipA

@[expose] public section

section

open Matrix Formalism.L2.NG ReciprocityTheory.Aut Formalism.AUTREP NumberField GlobalTheory.AlgWtHW

namespace GlobalTheory.AlgWtHW

theorem mulVec_mem_sle_of_isBEig : ∀ (n : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] (Φ : GL (Fin n) ℂ → Matrix ι ι ℂ), IsPolyRep Φ → ∀ (v : ι → ℂ) (lam : Fin n → ℤ), IsBEig Φ v lam → ∀ B : GL (Fin n) ℂ, Φ B *ᵥ v ∈ Sle Φ lam := by
  intro n ι _ _ Φ hΦ v lam hv B
  have hdom : DomLE lam lam := ⟨rfl, fun _ => le_rfl⟩
  have hvS : v ∈ Sle Φ lam := by
    refine Submodule.subset_span ⟨lam, hdom, fun D hD => hv.2 D ?_⟩
    intro a b hab
    exact hD (ne_of_gt hab)

  have hstab : ∀ L : GL (Fin n) ℂ, L.val.BlockTriangular OrderDual.toDual →
      ∀ w ∈ Sle Φ lam, Φ L *ᵥ w ∈ Sle Φ lam := by
    refine GlobalTheory.T.lowerTriangular_GL_complex_induction _ ?_ ?_ ?_ ?_
    · intro w hw; rw [hΦ.one, one_mulVec]; exact hw
    · intro A C hA hC w hw
      rw [hΦ.mul, ← mulVec_mulVec]
      exact hA _ (hC w hw)
    · intro D hD w hw
      refine Submodule.span_induction (p := fun w _ => Φ D *ᵥ w ∈ Sle Φ lam) ?_ ?_ ?_ ?_ hw
      · rintro u ⟨ν, hν, hu⟩
        rw [hu D hD]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨ν, hν, hu⟩)
      · simp
      · intro x y _ _ hx hy; rw [mulVec_add]; exact Submodule.add_mem _ hx hy
      · intro c x _ hx; rw [mulVec_smul]; exact Submodule.smul_mem _ _ hx
    · intro i j s T hji hT w hw
      refine Submodule.span_induction (p := fun w _ => Φ T *ᵥ w ∈ Sle Φ lam) ?_ ?_ ?_ ?_ hw
      · rintro u ⟨ν, hν, hu⟩
        exact GlobalTheory.T.lowerTransvection_mulVec_mem_spanWeightVectorsDominatedBy Φ hΦ lam ν hν u hu i j hji s T hT
      · simp
      · intro x y _ _ hx hy; rw [mulVec_add]; exact Submodule.add_mem _ hx hy
      · intro c x _ hx; rw [mulVec_smul]; exact Submodule.smul_mem _ _ hx

  have hbig : ∀ C : GL (Fin n) ℂ,
      (∀ (k : ℕ) (hk : k ≤ n), (C.val.submatrix (Fin.castLE hk) (Fin.castLE hk)).det ≠ 0) →
      Φ C *ᵥ v ∈ Sle Φ lam := by
    intro C hC
    obtain ⟨L, U, hL, hU, rfl⟩ := GlobalTheory.T.exists_LU_decomposition_of_leading_minors_ne_zero C hC
    rw [hΦ.mul, ← mulVec_mulVec, hv.2 U hU, mulVec_smul]
    exact Submodule.smul_mem _ _ (hstab L hL v hvS)

  refine GlobalTheory.T.polyRep_mulVec_mem_of_cofinite_scalar_shift Φ hΦ _ v B _ (GlobalTheory.T.finite_shifts_vanishing_leading_minor B.val) ?_
  intro s hs C hC
  apply hbig
  rw [hC]
  simpa using hs

end GlobalTheory.AlgWtHW
end

section

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal GlobalTheory.NormCompat

namespace GlobalTheory.NormCompat

theorem prod_zpow_const {ι B : Type} [CommGroup B] (c : B) (s : Finset ι) (e : ι → ℤ) :
    ∏ i ∈ s, c ^ e i = c ^ (∑ i ∈ s, e i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih => rw [Finset.prod_insert hj, Finset.sum_insert hj, ih, zpow_add]

theorem finite_setOf_valuation_ne_one (F : Type) [Field F] [NumberField F] (x : Fˣ) :
    {v : HeightOneSpectrum (𝓞 F) | v.valuation F (x : F) ≠ 1}.Finite := by
  refine ((HeightOneSpectrum.Support.finite (𝓞 F) (x : F)).union
    (HeightOneSpectrum.Support.finite (𝓞 F) ((x : F)⁻¹))).subset ?_
  intro v hv
  have h0 : v.valuation F (x : F) ≠ 0 := by simp
  rcases lt_or_gt_of_ne hv with h | h
  · right
    show 1 < v.valuation F ((x : F)⁻¹)
    rw [map_inv₀]
    exact (one_lt_inv₀ (zero_lt_iff.2 h0)).2 h
  · left
    exact h

theorem valued_locUnit (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (b : Fˣ) :
    Valued.v ((Units.map (algebraMap F (v.adicCompletion F)).toMonoidHom b : (v.adicCompletion F)ˣ) :
      v.adicCompletion F) = v.valuation F (b : F) := by
  show Valued.v ((b : F) : v.adicCompletion F) = _
  exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v _

theorem map_locUnit_eq_zpow {F B : Type} [Field F] [NumberField F] [CommGroup B] (ψ : Ideles F →* B)
    (v : HeightOneSpectrum (𝓞 F)) (hu : ∀ x, IsUnitAt v x → ψ (localIdele F v x) = 1)
    (ϖ : (v.adicCompletion F)ˣ) (hϖ : IsUnifAt v ϖ) (b : Fˣ) :
    ψ (locUnit F v b) = ψ (localIdele F v ϖ) ^ ordF v b := by
  set x : (v.adicCompletion F)ˣ := Units.map (algebraMap F (v.adicCompletion F)).toMonoidHom b with hx
  have hb0 : v.valuation F (b : F) ≠ 0 := by simp
  have hu' : IsUnitAt v (x * ϖ ^ (-ordF v b)) := by
    unfold IsUnitAt
    rw [Units.val_mul, Units.val_zpow_eq_zpow_val, map_mul, map_zpow₀, hx, valued_locUnit, hϖ, ordF, neg_neg,
      ← WithZero.exp_zsmul, ← WithZero.exp_log hb0, ← WithZero.exp_add, WithZero.log_exp]
    simp
  have h := hu _ hu'
  rw [map_mul, map_mul, map_zpow, map_zpow, zpow_neg, mul_inv_eq_one] at h
  rw [locUnit_apply, ← hx]
  exact h

end GlobalTheory.NormCompat

namespace GlobalTheory.NormCompat

theorem under_eq_iff {E K : Type} [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K]
    (w : HeightOneSpectrum (𝓞 K)) (v : HeightOneSpectrum (𝓞 E)) :
    w.under (𝓞 E) = v ↔ w.asIdeal.comap (algebraMap (𝓞 E) (𝓞 K)) = v.asIdeal := by
  constructor
  · rintro rfl; rfl
  · intro h; exact HeightOneSpectrum.ext h

theorem finite_setOf_under_eq {E K : Type} [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K]
    (v : HeightOneSpectrum (𝓞 E)) : {w : HeightOneSpectrum (𝓞 K) | w.under (𝓞 E) = v}.Finite := by
  have h0 : Ideal.map (algebraMap (𝓞 E) (𝓞 K)) v.asIdeal ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.map_eq_bot_iff_of_injective (FaithfulSMul.algebraMap_injective _ _)]
    exact v.ne_bot
  refine (Ideal.finite_factors h0).subset fun w hw => ?_
  simp only [Set.mem_setOf_eq] at hw ⊢
  rw [Ideal.dvd_iff_le, Ideal.map_le_iff_le_comap, ← (under_eq_iff w v).mp hw]

end GlobalTheory.NormCompat

namespace GlobalTheory.NormCompat

theorem prod_locUnit_eq_prod_locUnit_norm : ∀ (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K] (B : Type) [CommGroup B] (ψ1 : Ideles K →* B) (ψ2 : Ideles E →* B) (S : Finset (HeightOneSpectrum (𝓞 E))), (∀ v ∉ S, ∀ x, IsUnitAt v x → ψ2 (localIdele E v x) = 1) → (∀ v ∉ S, ∀ w : HeightOneSpectrum (𝓞 K), w.asIdeal.comap (algebraMap (𝓞 E) (𝓞 K)) = v.asIdeal → ∀ x, IsUnitAt w x → ψ1 (localIdele K w x) = 1) → (∀ v ∉ S, ∀ w : HeightOneSpectrum (𝓞 K), w.asIdeal.comap (algebraMap (𝓞 E) (𝓞 K)) = v.asIdeal → ∀ x ϖ, IsUnifAt w x → IsUnifAt v ϖ → ψ1 (localIdele K w x) = ψ2 (localIdele E v ϖ) ^ w.asIdeal.inertiaDeg (𝓞 E)) → ∀ a : Kˣ, ∃ (TK : Finset (HeightOneSpectrum (𝓞 K))) (TE : Finset (HeightOneSpectrum (𝓞 E))), (∀ w ∈ TK, ∀ v ∈ S, w.asIdeal.comap (algebraMap (𝓞 E) (𝓞 K)) ≠ v.asIdeal) ∧ (∀ w ∉ TK, (∀ v ∈ S, w.asIdeal.comap (algebraMap (𝓞 E) (𝓞 K)) ≠ v.asIdeal) → ψ1 (locUnit K w a) = 1) ∧ (∀ v ∈ TE, v ∉ S) ∧ (∀ v ∉ TE, v ∉ S → ψ2 (locUnit E v (Units.map (Algebra.norm E (S := K)) a)) = 1) ∧ ∏ w ∈ TK, ψ1 (locUnit K w a) = ∏ v ∈ TE, ψ2 (locUnit E v (Units.map (Algebra.norm E (S := K)) a)) := by
  classical
  intro E K _ _ _ _ _ B _ ψ1 ψ2 S h2u h1u h1f a
  set Na : Eˣ := Units.map (Algebra.norm E (S := K)) a with hNa
  have hfinE : ((fun w : HeightOneSpectrum (𝓞 K) => w.under (𝓞 E)) ''
      {w | w.valuation K (a : K) ≠ 1} ∪ {v : HeightOneSpectrum (𝓞 E) | v.valuation E (Na : E) ≠ 1}).Finite :=
    ((finite_setOf_valuation_ne_one K a).image _).union (finite_setOf_valuation_ne_one E Na)
  set TE : Finset (HeightOneSpectrum (𝓞 E)) := hfinE.toFinset.filter (· ∉ S) with hTE
  set TK : Finset (HeightOneSpectrum (𝓞 K)) :=
    TE.biUnion (fun v => (finite_setOf_under_eq (K := K) v).toFinset) with hTK
  have memTK : ∀ w, w ∈ TK ↔ w.under (𝓞 E) ∈ TE := by
    intro w
    simp only [hTK, Finset.mem_biUnion, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
    exact ⟨fun ⟨v, hv, h⟩ => h ▸ hv, fun h => ⟨_, h, rfl⟩⟩
  have memTE : ∀ v, v ∈ TE ↔ v ∉ S ∧ ((∃ w : HeightOneSpectrum (𝓞 K), w.valuation K (a : K) ≠ 1 ∧
      w.under (𝓞 E) = v) ∨ v.valuation E (Na : E) ≠ 1) := by
    intro v
    simp only [hTE, Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_union, Set.mem_image, Set.mem_setOf_eq]
    exact and_comm
  have hcomap : ∀ w : HeightOneSpectrum (𝓞 K),
      w.asIdeal.comap (algebraMap (𝓞 E) (𝓞 K)) = (w.under (𝓞 E)).asIdeal := fun w => rfl
  refine ⟨TK, TE, ?_, ?_, ?_, ?_, ?_⟩
  · intro w hw v hv h
    have := ((memTE _).mp ((memTK w).mp hw)).1
    rw [(under_eq_iff w v).mpr h] at this
    exact this hv
  · intro w hw hS
    have hS' : w.under (𝓞 E) ∉ S := fun h => hS _ h (hcomap w)
    have hval : w.valuation K (a : K) = 1 := by
      by_contra h
      exact hw ((memTK w).mpr ((memTE _).mpr ⟨hS', Or.inl ⟨w, h, rfl⟩⟩))
    rw [locUnit_apply]
    refine h1u _ hS' w (hcomap w) _ ?_
    unfold IsUnitAt
    rw [valued_locUnit, hval]
  · intro v hv
    exact ((memTE v).mp hv).1
  · intro v hv hS
    have hval : v.valuation E (Na : E) = 1 := by
      by_contra h
      exact hv ((memTE v).mpr ⟨hS, Or.inr h⟩)
    rw [locUnit_apply]
    refine h2u v hS _ ?_
    unfold IsUnitAt
    rw [valued_locUnit, hval]
  ·
    set c : HeightOneSpectrum (𝓞 E) → B := fun v => ψ2 (localIdele E v (atFin v (unif v))) with hc
    have hK : ∀ w ∈ TK, ψ1 (locUnit K w a) =
        c (w.under (𝓞 E)) ^ ((w.asIdeal.inertiaDeg (𝓞 E) : ℤ) * ordF w a) := by
      intro w hw
      have hS : w.under (𝓞 E) ∉ S := ((memTE _).mp ((memTK w).mp hw)).1
      rw [map_locUnit_eq_zpow ψ1 w (h1u _ hS w (hcomap w)) _ (unif_spec w),
        h1f _ hS w (hcomap w) _ _ (unif_spec w) (unif_spec _), zpow_mul, zpow_natCast]
    have hE : ∀ v ∈ TE, ψ2 (locUnit E v Na) = c v ^ ordF v Na := by
      intro v hv
      exact map_locUnit_eq_zpow ψ2 v (h2u v ((memTE v).mp hv).1) _ (unif_spec v) Na
    rw [Finset.prod_congr rfl hK, Finset.prod_congr rfl hE,
      ← Finset.prod_fiberwise_of_maps_to (g := fun w : HeightOneSpectrum (𝓞 K) => w.under (𝓞 E))
        (t := TE) (fun w hw => (memTK w).mp hw)]
    refine Finset.prod_congr rfl fun v hv => ?_
    have hfib : ∀ w ∈ TK.filter (fun w => w.under (𝓞 E) = v), c (w.under (𝓞 E)) = c v := by
      intro w hw
      rw [(Finset.mem_filter.mp hw).2]
    rw [Finset.prod_congr rfl fun w hw => by rw [hfib w hw], prod_zpow_const]
    congr 1
    have hs : ∀ w, w ∈ TK.filter (fun w => w.under (𝓞 E) = v) ↔
        w.asIdeal.comap (algebraMap (𝓞 E) (𝓞 K)) = v.asIdeal := by
      intro w
      rw [Finset.mem_filter, ← under_eq_iff]
      constructor
      · exact fun h => h.2
      · intro h
        exact ⟨(memTK w).mpr (h ▸ hv), h⟩
    have key := GlobalTheory.T.intValuation_norm_eq_sum_residueDegree_mul E K v a _ hs
    simp only [ordF, hNa, Units.coe_map, MonoidHom.coe_coe] at key ⊢
    rw [key, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun w _ => ?_
    ring

end GlobalTheory.NormCompat

end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.UG Matrix
open scoped TensorProduct

namespace GlobalTheory.Mem.LocalDualBase

theorem localDual_eq_add_span : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (w : HeightOneSpectrum (𝓞 F)) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (L : Submodule (𝓞 E) (Fin n → E)) (p : 𝓞 E), J = 1 → p ≠ 0 → (∀ x, x ∈ L ↔ ∀ j : Fin n, ∃ r : 𝓞 E, x j = (r : E) ∧ (j.1 + 1 = n → p ∣ r)) → (∀ x, σ (σ x) = x) → ∃ e : latS (F := F) (w.adicCompletion F) (intV E w) (Submodule.span (𝓞 E) (dualSet (σ : E →+* E) J L)), ∀ t : latS (F := F) (w.adicCompletion F) (intV E w) (Submodule.span (𝓞 E) (dualSet (σ : E →+* E) J L)), ∃ s : intV E w, (t - s • e).1 ∈ latS (F := F) (w.adicCompletion F) (intV E w) L := by
  intro F E _ _ _ _ _ σ w n J L p hJ hp hL _
  subst hJ
  have hform1 : ∀ x y : Fin n → E, hform (σ : E →+* E) (1 : Matrix (Fin n) (Fin n) E) x y = ∑ i, σ (x i) * y i := by
    intro x y
    unfold hform
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [Matrix.one_apply]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · refine ⟨0, fun t => ⟨0, ?_⟩⟩
    have : (t - (0 : intV E w) • (0 : latS (F := F) (w.adicCompletion F) (intV E w)
        (Submodule.span (𝓞 E) (dualSet (σ : E →+* E) (1 : Matrix (Fin 0) (Fin 0) E) L)))).1 = 0 :=
      Subsingleton.elim _ _
    rw [this]
    exact Submodule.zero_mem _

  set R := w.adicCompletion F
  let l : Fin n := ⟨n - 1, by omega⟩
  have hl : l.1 + 1 = n := by simp [l]; omega
  have hσO : ∀ r : 𝓞 E, σ (r : E) ∈ (algebraMap (𝓞 E) E).range := fun r =>
    ⟨⟨σ (r : E), map_isIntegral_int σ (RingOfIntegers.isIntegral_coe r)⟩, rfl⟩
  obtain ⟨pb, hpb⟩ := hσO p
  have hpb0 : (algebraMap (𝓞 E) E pb) ≠ 0 := by
    rw [hpb]
    intro h
    exact hp (by simpa using (map_eq_zero σ).1 h)
  set e0 : Fin n → E := Pi.single l (algebraMap (𝓞 E) E pb)⁻¹ with he0def
  have he0 : e0 ∈ dualSet (σ : E →+* E) (1 : Matrix (Fin n) (Fin n) E) L := by
    intro x hx
    rw [hform1, Finset.sum_eq_single l (by intro b _ hb; simp [e0, hb]) (by simp)]
    obtain ⟨r, hr, hd⟩ := (hL x).1 hx l
    obtain ⟨s, rfl⟩ := hd hl
    obtain ⟨u, hu⟩ := hσO s
    refine ⟨u, ?_⟩
    rw [hu, hr]
    simp only [e0, Pi.single_eq_same]
    push_cast
    rw [map_mul, ← hpb]
    field_simp
  have hglob : ∀ y ∈ Submodule.span (𝓞 E) (dualSet (σ : E →+* E) (1 : Matrix (Fin n) (Fin n) E) L),
      ∃ r : 𝓞 E, y - (algebraMap (𝓞 E) E r) • e0 ∈ L := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      have hxl : Pi.single l (p : E) ∈ L := by
        refine (hL _).2 fun i => ?_
        by_cases h : i = l
        · subst h
          exact ⟨p, by simp, fun _ => dvd_rfl⟩
        · exact ⟨0, by simp [h], fun _ => dvd_zero _⟩
      have h1 := hy _ hxl
      rw [hform1, Finset.sum_eq_single l (by intro b _ hb; simp [hb]) (by simp)] at h1
      simp only [Pi.single_eq_same] at h1
      obtain ⟨r, hr⟩ := h1
      refine ⟨r, (hL _).2 fun j => ?_⟩
      by_cases hj : j = l
      · subst hj
        refine ⟨0, ?_, fun _ => dvd_zero _⟩
        simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, e0, Pi.single_eq_same, hr, ← hpb]
        push_cast
        field_simp
        ring
      · have hxj : Pi.single j (1 : E) ∈ L := by
          refine (hL _).2 fun i => ?_
          by_cases h : i = j
          · subst h
            exact ⟨1, by simp, fun hi => absurd (Fin.ext (by omega)) hj⟩
          · exact ⟨0, by simp [h], fun _ => dvd_zero _⟩
        have h2 := hy _ hxj
        rw [hform1, Finset.sum_eq_single j (by intro b _ hb; simp [hb]) (by simp)] at h2
        simp only [Pi.single_eq_same, map_one, one_mul] at h2
        obtain ⟨u, hu⟩ := h2
        refine ⟨u, ?_, fun hj' => absurd (Fin.ext (by omega)) hj⟩
        simp [e0, hj, hu]
    | zero => exact ⟨0, by simp⟩
    | add y z _ _ h1 h2 =>
      obtain ⟨r1, hr1⟩ := h1
      obtain ⟨r2, hr2⟩ := h2
      refine ⟨r1 + r2, ?_⟩
      have : y + z - (algebraMap (𝓞 E) E (r1 + r2)) • e0 =
          (y - (algebraMap (𝓞 E) E r1) • e0) + (z - (algebraMap (𝓞 E) E r2) • e0) := by
        rw [map_add (f := _), add_smul]; abel
      rw [this]
      exact L.add_mem hr1 hr2
    | smul c y _ h =>
      obtain ⟨r, hr⟩ := h
      refine ⟨c * r, ?_⟩
      have : c • y - (algebraMap (𝓞 E) E (c * r)) • e0 = c • (y - (algebraMap (𝓞 E) E r) • e0) := by
        ext j
        simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, map_mul]
        simp only [Algebra.smul_def]
        ring
      rw [this]
      exact L.smul_mem c hr
  have hincl : ∀ r : 𝓞 E, inclE (F := F) R (algebraMap (𝓞 E) E r) ∈ intV E w := by
    intro r
    exact Subring.subset_closure (Or.inl ⟨⟨_, r, rfl⟩, rfl⟩)
  refine ⟨⟨fun i => inclE (F := F) R (e0 i),
    Submodule.subset_span ⟨e0, Submodule.subset_span he0, rfl⟩⟩, fun t => ?_⟩
  obtain ⟨t, ht⟩ := t
  suffices H : ∃ s : intV E w, t - (s : E ⊗[F] R) • (fun i => inclE (F := F) R (e0 i)) ∈
      latS (F := F) R (intV E w) L by
    obtain ⟨s, hs⟩ := H
    exact ⟨s, hs⟩
  induction ht using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨y', hy', rfl⟩ := hy
    obtain ⟨r, hr⟩ := hglob y' hy'
    refine ⟨⟨_, hincl r⟩, ?_⟩
    have : (fun i => inclE (F := F) R (y' i)) - inclE (F := F) R (algebraMap (𝓞 E) E r) •
        (fun i => inclE (F := F) R (e0 i)) =
        fun i => inclE (F := F) R ((y' - (algebraMap (𝓞 E) E r) • e0) i) := by
      ext i
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, map_sub, map_mul]
    rw [this]
    exact Submodule.subset_span ⟨_, hr, rfl⟩
  | zero => exact ⟨0, by simp⟩
  | add x y _ _ h1 h2 =>
    obtain ⟨s1, hs1⟩ := h1
    obtain ⟨s2, hs2⟩ := h2
    refine ⟨s1 + s2, ?_⟩
    have : x + y - ((s1 + s2 : intV E w) : E ⊗[F] R) • (fun i => inclE (F := F) R (e0 i)) =
        (x - (s1 : E ⊗[F] R) • (fun i => inclE (F := F) R (e0 i))) +
        (y - (s2 : E ⊗[F] R) • (fun i => inclE (F := F) R (e0 i))) := by
      rw [Subring.coe_add, add_smul]; abel
    rw [this]
    exact Submodule.add_mem _ hs1 hs2
  | smul a x _ h =>
    obtain ⟨s, hs⟩ := h
    refine ⟨a * s, ?_⟩
    have : a • x - ((a * s : intV E w) : E ⊗[F] R) • (fun i => inclE (F := F) R (e0 i)) =
        a • (x - (s : E ⊗[F] R) • (fun i => inclE (F := F) R (e0 i))) := by
      rw [Subring.coe_mul, mul_smul, smul_sub]
      rfl
    rw [this]
    exact Submodule.smul_mem _ a hs

end GlobalTheory.Mem.LocalDualBase
end

section

open Formalism.BasicNotions MeasureTheory Filter Topology Matrix

namespace GlobalTheory.OmegaLebUnique

theorem omegaLeb_unique :
    ∀ (P Q : ℕ) (l l' : Measure (lieU P Q)), IsOmegaLeb l → IsOmegaLeb l' → l = l' :=
  fun _ _ _ _ h h' => GlobalTheory.CompactDualUnique.isOmegaLeb_unique h h'

end GlobalTheory.OmegaLebUnique
end

section

open Formalism.ConjugateSelfDual Formalism.MainNotions.N Polynomial

namespace GlobalTheory

theorem lift_rep_of_entries_in_image : ∀ {k L Γ : Type} [Field k] [Field L] [Group Γ] (f : k →+* L) {b : ℕ} (τ : Γ →* GL (Fin b) L), (∀ g i j, ∃ x, f x = ((τ g : GL (Fin b) L) : Matrix (Fin b) (Fin b) L) i j) → ∃ σ : Γ →* GL (Fin b) k, mapRep f σ = τ := by
  intro k L Γ _ _ _ f b τ h
  choose pre hpre using h
  have hinj : Function.Injective (f.mapMatrix : Matrix (Fin b) (Fin b) k →+* Matrix (Fin b) (Fin b) L) :=
    Matrix.map_injective f.injective
  have key : ∀ g, f.mapMatrix (Matrix.of (pre g)) = ((τ g : GL (Fin b) L) : Matrix (Fin b) (Fin b) L) := by
    intro g; ext i j; simp [RingHom.mapMatrix_apply, Matrix.map_apply, hpre]
  let m : Γ →* Matrix (Fin b) (Fin b) k :=
    { toFun := fun g => Matrix.of (pre g)
      map_one' := hinj (by rw [key, map_one, map_one]; rfl)
      map_mul' := fun x y => hinj (by rw [map_mul, key, key, key, map_mul]; rfl) }
  refine ⟨MonoidHom.toHomUnits m, ?_⟩
  ext g i j
  simp only [mapRep, MonoidHom.comp_apply, Units.coe_map, MonoidHom.coe_coe]
  rw [MonoidHom.coe_toHomUnits]
  exact congrFun (congrFun (key g) i) j

end GlobalTheory
end

section


theorem _root_.GlobalTheory.T.exists_holomorphic_extension_across_coordinate_hyperplanes : ∀ (n a : ℕ) (ρ : ℝ) (Φ : (Fin n → ℂ) → ℂ) (m : Fin n → ℕ), 0 < ρ → DifferentiableOn ℂ Φ {z | z ∈ Metric.ball (0 : Fin n → ℂ) ρ ∧ ∀ k : Fin n, (k : ℕ) < a → z k ≠ 0} → (∀ z ∈ Metric.ball (0 : Fin n → ℂ) ρ, (∀ k : Fin n, (k : ℕ) < a → z k ≠ 0) → ‖Complex.exp (2 * Real.pi * Complex.I * Φ z)‖ * ∏ k, ‖z k‖ ^ m k ≤ 1) → ∃ F : (Fin n → ℂ) → ℂ, DifferentiableOn ℂ F (Metric.ball 0 ρ) ∧ ∀ z ∈ Metric.ball (0 : Fin n → ℂ) ρ, (∀ k : Fin n, (k : ℕ) < a → z k ≠ 0) → F z = Φ z := by
  first | exact @GlobalTheory.HyperplaneExt.extension_across_coordinate_hyperplanes | exact GlobalTheory.HyperplaneExt.extension_across_coordinate_hyperplanes | (intros; apply GlobalTheory.HyperplaneExt.extension_across_coordinate_hyperplanes <;> assumption)
end

section

open IsLocalRing

theorem _root_.GlobalTheory.T.finite_integralClosure_of_essFiniteType_int_domain : ∀ (D : Type) [CommRing D] [IsDomain D] [Algebra.EssFiniteType ℤ D], Module.Finite D (integralClosure D (FractionRing D)) := by
  first | exact @GlobalTheory.finite_integralClosure_of_essFiniteType_int | exact GlobalTheory.finite_integralClosure_of_essFiniteType_int | (intros; apply GlobalTheory.finite_integralClosure_of_essFiniteType_int <;> assumption)
end
