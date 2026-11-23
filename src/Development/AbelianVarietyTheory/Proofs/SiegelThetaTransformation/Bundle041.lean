module

public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsWeakOfDatum
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsCompactLatticeStabilizerBoundedReal
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle086
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle074
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle084
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle018
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle079
public import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.LevelStructureProperties
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.StrongApproximationUnitaryCongruence
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.TensorLatticeSelfDualSemicharacterIndex
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle032
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.TensorLatticeVacuaExistUnique
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle031
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsStabForm
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle008
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle001

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker
open GlobalTheory.SW hiding Level
open GlobalTheory.Dict (hx pv)
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)
open scoped TensorProduct ComplexConjugate Real Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Ker.CongTop

variable {D : D7}

theorem fmt_eq (V : HSp D) (g : GA D V) : fmt V g = (finHom V g).1 := rfl

theorem fmt_one (V : HSp D) : fmt V 1 = 1 := by rw [fmt_eq, map_one, Units.val_one]

theorem fmt_mul (V : HSp D) (g h : GA D V) : fmt V (g * h) = fmt V g * fmt V h := by
  rw [fmt_eq, map_mul, Units.val_mul, fmt_eq, fmt_eq]

theorem isMov_iff (V : HSp D) (L : Lt D.host.E V.rank) (k : GA D V) :
    IsMov (fmt V k) L L ↔ (∀ u ∈ hatV L, fmt V k *ᵥ u ∈ hatV L) ∧ ∀ u ∈ hatV L, fmt V k⁻¹ *ᵥ u ∈ hatV L := by
  constructor
  · intro h
    refine ⟨fun u hu => (h _).2 ⟨u, hu, rfl⟩, fun u hu => ?_⟩
    obtain ⟨u₀, h0, rfl⟩ := (h u).1 hu
    rwa [Matrix.mulVec_mulVec, ← fmt_mul, inv_mul_cancel, fmt_one, Matrix.one_mulVec]
  · rintro ⟨h1, h2⟩ u
    constructor
    · intro hu
      refine ⟨_, h2 u hu, ?_⟩
      rw [Matrix.mulVec_mulVec, ← fmt_mul, mul_inv_cancel, fmt_one, Matrix.one_mulVec]
    · rintro ⟨u₀, h0, rfl⟩
      exact h1 _ h0

noncomputable def congSub (V : HSp D) (L : Lt D.host.E V.rank) (M : ℕ) : Subgroup (GA D V) where
  carrier := {k | CongK V L M k}
  one_mem' := by
    refine ⟨(isMov_iff V L 1).2 ⟨fun u hu => ?_, fun u hu => ?_⟩, fun u _ => ⟨0, zero_mem _, ?_⟩⟩
    · rwa [fmt_one, Matrix.one_mulVec]
    · rwa [inv_one, fmt_one, Matrix.one_mulVec]
    · rw [fmt_one, Matrix.one_mulVec, sub_self, nsmul_zero]
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    rw [isMov_iff] at ha hb
    refine ⟨(isMov_iff V L _).2 ⟨fun u hu => ?_, fun u hu => ?_⟩, fun u hu => ?_⟩
    · rw [fmt_mul, ← Matrix.mulVec_mulVec]
      exact ha.1 _ (hb.1 _ hu)
    · rw [_root_.mul_inv_rev, fmt_mul, ← Matrix.mulVec_mulVec]
      exact hb.2 _ (ha.2 _ hu)
    · obtain ⟨x, hx, ex⟩ := ha' _ (hb.1 _ hu)
      obtain ⟨y, hy, ey⟩ := hb' _ hu
      refine ⟨x + y, add_mem hx hy, ?_⟩
      rw [fmt_mul, ← Matrix.mulVec_mulVec, nsmul_add, ← ex, ← ey, sub_add_sub_cancel]
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    rw [isMov_iff] at ha
    refine ⟨(isMov_iff V L _).2 ⟨ha.2, by rw [inv_inv]; exact ha.1⟩, fun u hu => ?_⟩
    obtain ⟨x, hx, ex⟩ := ha' _ (ha.2 _ hu)
    refine ⟨-x, neg_mem hx, ?_⟩
    rw [Matrix.mulVec_mulVec, ← fmt_mul, mul_inv_cancel, fmt_one, Matrix.one_mulVec] at ex
    rw [neg_nsmul, ← ex, neg_sub]

theorem isOpen_congSub (V : HSp D) (L : Lt D.host.E V.rank) (M : ℕ) (hfg : L.FG)
    (hsp : Submodule.span D.host.E (L : Set (Fin V.rank → D.host.E)) = ⊤) (hM : 0 < M) :
    IsOpen (congSub V L M : Set (GA D V)) := by
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA D.sp.cm.sig V.gram
  have hn : {m : Matrix (Fin V.rank) (Fin V.rank) (AfE D) | ∀ z ∈ hatV L, ∃ y ∈ hatV L, m *ᵥ z - z = M • y} ∈
      nhds (1 : Matrix (Fin V.rank) (Fin V.rank) (AfE D)) :=
    GlobalTheory.LevelOpen.congr_mem_nhds D.host.F D.host.E V.rank _ hfg hsp M hM
  have hc : Continuous (fmt V) := GlobalTheory.Member.continuous_finHom_val D V
  have h1 := hc.continuousAt (x := 1) |>.preimage_mem_nhds (by rw [fmt_one]; exact hn)
  have h2 := (hc.comp continuous_inv).continuousAt (x := 1) |>.preimage_mem_nhds
    (by rw [Function.comp_apply, inv_one, fmt_one]; exact hn)
  refine Subgroup.isOpen_of_mem_nhds _ (g := 1) ?_
  refine Filter.mem_of_superset (Filter.inter_mem h1 h2) ?_
  rintro k ⟨hk1, hk2⟩
  refine ⟨(isMov_iff V L k).2 ⟨fun y hy => ?_, fun y hy => ?_⟩, hk1⟩
  · obtain ⟨w, hw, h⟩ := hk1 y hy
    rw [eq_add_of_sub_eq h]
    exact add_mem (nsmul_mem hw M) hy
  · obtain ⟨w, hw, h⟩ := hk2 y hy
    rw [Function.comp_apply] at h
    rw [eq_add_of_sub_eq h]
    exact add_mem (nsmul_mem hw M) hy

theorem isClosed_GinfC (V : HSp D) : IsClosed (GinfC V : Set (GA D V)) := by
  haveI : Module.Finite D.host.F D.host.E := Module.Finite.of_restrictScalars_finite ℚ _ _
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_finiteAdeleRing_of_numberField D.host.F
  obtain ⟨e⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := D.host.F) (E := D.host.E) (Af D.host.F)
  haveI : T2Space (Af D.host.F ⊗[D.host.F] D.host.E) := e.isEmbedding.t2Space
  have h : (GinfC V : Set (GA D V)) = {g | (finHom V g).1 = 1} := by
    ext g
    exact Units.ext_iff
  rw [h]
  exact isClosed_eq (GlobalTheory.Member.continuous_finHom_val D V) continuous_const

theorem isClosed_GfC (V : HSp D) : IsClosed (GfC V : Set (GA D V)) := by
  haveI : Module.Finite D.host.F D.host.E := Module.Finite.of_restrictScalars_finite ℚ _ _
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_infiniteAdeleRing_of_numberField_field D.host.F
  obtain ⟨e⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := D.host.F) (E := D.host.E) (Ainf D.host.F)
  haveI : T2Space (Ainf D.host.F ⊗[D.host.F] D.host.E) := e.isEmbedding.t2Space
  have h : (GfC V : Set (GA D V)) = {g | (infHom V g).1 = 1} := by
    ext g
    exact Units.ext_iff
  rw [h]
  have hm : Continuous (fun k : GA D V => (matHom V k).1) :=
    Units.continuous_val.comp continuous_subtype_val
  exact isClosed_eq (hm.matrix_map (GlobalTheory.Member.continuous_infPart D)) continuous_const

theorem exists_compact (V : HSp D) (L : Lt D.host.E V.rank) (hfg : L.FG)
    (hsp : Submodule.span D.host.E (L : Set (Fin V.rank → D.host.E)) = ⊤) :
    ∃ C : Set (GA D V), IsCompact C ∧ ∀ k : GA D V, IsMov (fmt V k) L L → (k ∈ GfC V ∨ V.gram = 1) → k ∈ C := by
  obtain ⟨θ₀, hθ₀⟩ := (GlobalTheory.Member.infiniteAdele_bijective D).1
  let θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ) := fun ρ => θ₀ (tauE D ρ)
  have hθ : IsInfFam θ := fun ρ => hθ₀ _
  have hsp' := (GlobalTheory.Member.Arch.archM_spec D V θ₀ hθ₀).1
  have hu : ∀ ρ h, (infMat D.sp.cm.sig V.gram (θ ρ) h)ᴴ * gramAt D V ρ * infMat D.sp.cm.sig V.gram (θ ρ) h =
      gramAt D V ρ := fun ρ h => (GlobalTheory.Member.Arch.unit_iff _ _ _).1 ((hsp' (tauE D ρ)).2.2.2.2 h)
  obtain ⟨C, hC, hCe⟩ := GlobalTheory.StabCompact.exists_compact_entries D.host.F D.host.E L hfg hsp
  obtain ⟨C', hC', hCe'⟩ := GlobalTheory.StabCompact.exists_compact_adele D θ hθ 1 C hC
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField D.host.F
  haveI : Module.Finite D.host.F D.host.E := Module.Finite.of_restrictScalars_finite ℚ _ _
  obtain ⟨K, hK, hKe⟩ := GlobalTheory.StabCompact.exists_compact_of_entries (AF D.host.F) D.sp.cm.sig V.gram
    (GlobalTheory.StabCompact.det_gram_ne_zero V) C' hC'
  refine ⟨K, hK, fun k h1 h2 => hKe k fun i j =>
    hCe' _ (hCe (fmt V k) ((isMov_iff V L k).1 h1).1 i j) fun ρ => ?_⟩
  have hU : infMat D.sp.cm.sig V.gram (θ ρ) k ∈ Matrix.unitaryGroup (Fin V.rank) ℂ := by
    rcases h2 with h2 | h2
    · have h3 : (infHom V k).1 = 1 := congrArg Units.val (show infHom V k = 1 from h2)
      have h4 : infMat D.sp.cm.sig V.gram (θ ρ) k = ((infHom V k).1).map (θ ρ) := rfl
      rw [h4, h3, Matrix.map_one _ (map_zero _) (map_one _)]
      exact one_mem _
    · have h3 : gramAt D V ρ = 1 := by
        unfold gramAt
        rw [h2, Matrix.map_one _ (map_zero _) (map_one _)]
      have h4 := hu ρ k
      rw [h3, Matrix.mul_one] at h4
      exact Matrix.mem_unitaryGroup_iff'.2 h4
  exact entry_norm_bound_of_unitary hU i j

theorem adelicUnitary_top_cong : ∀ (D : D7) (V : HSp D), IsTopologicalGroup (GA D V) ∧ LocallyCompactSpace (GA D V) ∧ SecondCountableTopology (GA D V) ∧ T2Space (GA D V) ∧ BorelSpace (GA D V) ∧ IsClosed (GinfC V : Set (GA D V)) ∧ ∀ (L : Lt D.host.E V.rank) (M : ℕ), (L.FG ∧ Submodule.span D.host.E (L : Set (Fin V.rank → D.host.E)) = ⊤) → 0 < M → ∃ K : Subgroup (GA D V), (∀ k, k ∈ K ↔ CongK V L M k) ∧ IsOpen (K : Set (GA D V)) ∧ IsCompact ((K : Set (GA D V)) ∩ GfC V) ∧ (V.gram = 1 → IsCompact (K : Set (GA D V))) := by
  intro D V
  obtain ⟨i1, i2, i3⟩ := GlobalTheory.AdelicUnitaryTop.lcsc_adelicUnitary D.host.F D.host.E D.sp.cm.sig V.rank V.gram
  have i0 := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA D.sp.cm.sig V.gram
  refine ⟨i0, i1, i2, i3, Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.borelHA D.sp.cm.sig V.gram, isClosed_GinfC V, ?_⟩
  rintro L M ⟨hfg, hsp⟩ hM
  have ho := isOpen_congSub V L M hfg hsp hM
  have hcl : IsClosed (congSub V L M : Set (GA D V)) := Subgroup.isClosed_of_isOpen _ ho
  obtain ⟨C, hC, hCm⟩ := exists_compact V L hfg hsp
  refine ⟨congSub V L M, fun _ => Iff.rfl, ho, ?_, fun hg => ?_⟩
  · exact hC.of_isClosed_subset (hcl.inter (isClosed_GfC V)) fun k hk => hCm k hk.1.1 (Or.inl hk.2)
  · exact hC.of_isClosed_subset hcl fun k hk => hCm k hk.1 (Or.inr hg)

end GlobalTheory.Ker.CongTop
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict

namespace GlobalTheory.Dict.Move

theorem exists_pow_le {E : Type} [Field E] [NumberField E] (𝔪 : Ideal (𝓞 E)) {d : 𝓞 E} (hd : d ≠ 0) :
    ∃ N : ℕ, ∃ t, IsCoprime (Ideal.span {t}) 𝔪 ∧ ∀ b ∈ 𝔪 ^ N, t * b ∈ Ideal.span {d} := by
  haveI : Finite (𝓞 E ⧸ Ideal.span {d}) :=
    Ideal.finiteQuotientOfFreeOfNeBot _ (by simpa using hd)
  haveI : IsArtinianRing (𝓞 E ⧸ Ideal.span {d}) := isArtinian_of_finite
  obtain ⟨N, hN⟩ := IsArtinian.monotone_stabilizes (R := 𝓞 E ⧸ Ideal.span {d}) (M := 𝓞 E ⧸ Ideal.span {d})
    ⟨fun n => OrderDual.toDual ((𝔪 ^ n).map (Ideal.Quotient.mk (Ideal.span {d}))),
      fun a b h => Ideal.map_mono (Ideal.pow_le_pow_right h)⟩
  have h1 : (𝔪 ^ N).map (Ideal.Quotient.mk (Ideal.span {d})) =
      (𝔪 ^ (N + 1)).map (Ideal.Quotient.mk (Ideal.span {d})) := hN (N + 1) (Nat.le_succ N)
  have h2 : 𝔪 ^ N ≤ Ideal.span {d} ⊔ 𝔪 • 𝔪 ^ N := by
    have := (Ideal.le_comap_map (f := Ideal.Quotient.mk (Ideal.span {d})) (I := 𝔪 ^ N))
    rw [h1, Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot,
      Ideal.mk_ker, sup_comm, pow_succ'] at this
    exact this
  exact ⟨N, Lev.nakayama (IsNoetherian.noetherian _) h2⟩

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {X : Data E r}

theorem exists_pow_smul {𝔪 : Ideal (𝓞 E)} (h0 : 𝔪 ≠ ⊥) (v : Fin r → E) :
    ∃ N : ℕ, ∀ b ∈ 𝔪 ^ N, b • v ∈ Lev.loc 𝔪 (𝔪 • X.Λ) := by
  obtain ⟨k, hk, hx⟩ := GlobalTheory.LatFin.exists_int_smul_mem X.Λ X.Λ_span v
  obtain ⟨m, hm, hm0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h0
  obtain ⟨N, t, ht, h⟩ := exists_pow_le 𝔪 (d := m * (k : 𝓞 E)) (mul_ne_zero hm0 (by exact_mod_cast hk))
  refine ⟨N, fun b hb => ⟨t, ht, ?_⟩⟩
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 (h b hb)
  rw [← mul_smul, ← hc, mul_smul, mul_smul, Int.cast_smul_eq_zsmul]
  exact Submodule.smul_mem _ _ (Submodule.smul_mem_smul hm hx)


omit [IsCMField E] in
theorem isUnit_cols {𝔪 : Ideal (𝓞 E)} (h1 : 𝔪 ≠ ⊤) {L : Lt E r} (hfg : L.FG)
    (hsp : Submodule.span E (L : Set (Fin r → E)) = ⊤) {u : Fin r → Fin r → E}
    (h : L ≤ Submodule.span (𝓞 E) (Set.range u) ⊔ 𝔪 • L) : IsUnit (Matrix.of u)ᵀ := by
  obtain ⟨s, hs, hN⟩ := Lev.nakayama hfg h
  have hs0 : (s : E) ≠ 0 := by simpa using Lev.cop_ne_zero h1 hs
  have hli : LinearIndependent E u := by
    refine linearIndependent_of_top_le_span_of_card_eq_finrank ?_ (by simp)
    rw [← hsp, Submodule.span_le]
    intro v hv
    have := Submodule.span_le_restrictScalars (𝓞 E) E _ (hN v hv)
    exact (Submodule.smul_mem_iff _ hs0).1 this
  exact Matrix.linearIndependent_cols_iff_isUnit.1 hli

theorem exists_cong (D : SW.Level X) {L : Lt E r} {u : Fin r → Fin r → E} (hL : SelfD X L)
    (h : L ≤ Submodule.span (𝓞 E) (Set.range u) ⊔ D.𝔪 • L) :
    ∃ ga : GL (Fin r) E, IsUn X ga ∧
      ∀ i, Cong X D.𝔪 ((ga : Matrix (Fin r) (Fin r) E) *ᵥ u i) (D.β i) := by
  obtain ⟨U, hU⟩ := isUnit_cols D.proper hL.1 (TensLat.span_of_selfD X hL) h
  obtain ⟨B, hB⟩ := isUnit_cols D.proper X.Λ_fg X.Λ_span D.β_span
  have hA (i) : ((B * U⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ u i = D.β i := by
    have e1 : u i = (U : Matrix (Fin r) (Fin r) E) *ᵥ Pi.single i 1 := by
      rw [hU]; funext k; simp
    rw [e1, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel_right, hB]
    funext k; simp
  choose N hN using fun p : Fin r × Fin r × Fin r =>
    exists_pow_smul (X := X) D.ne_bot (Pi.single p.2.1 (u p.1 p.2.2))
  obtain ⟨ga, hu, s, hs, hb⟩ := GlobalTheory.T.strong_approximation_unitary_congruence E r X D.𝔪 D.ne_bot D.cop (B * U⁻¹) (Finset.univ.sup N)
  choose b hb e using hb
  refine ⟨ga, hu, fun i => Lev.cong_iff.2 (Lev.loc_loc hs ?_)⟩
  have e2 : s • ((ga : Matrix (Fin r) (Fin r) E) *ᵥ u i - D.β i) =
      ∑ k, ∑ j, b k j • (Pi.single k (u i j) : Fin r → E) := by
    rw [← hA]
    funext k
    simp only [Lev.O_smul, Finset.sum_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, Pi.single_apply,
      Matrix.mulVec, dotProduct, ← e]
    rw [← Finset.sum_sub_distrib, Finset.smul_sum, Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_eq_single k (fun k' _ hk => by rw [if_neg (Ne.symm hk), mul_zero]) (by simp), if_pos rfl]
    change (s : E) * _ = _
    ring
  rw [e2]
  exact Submodule.sum_mem _ fun k _ => Submodule.sum_mem _ fun j _ =>
    hN (i, k, j) _ (Ideal.pow_le_pow_right (Finset.le_sup (Finset.mem_univ _)) (hb k j))

theorem mem_lats (D : SW.Level X) {L : Lt E r} {u : Fin r → Fin r → E} (hΛ : SelfD X X.Λ) (hL : SelfD X L)
    (hu : ∀ i, u i ∈ L) (h : L ≤ Submodule.span (𝓞 E) (Set.range u) ⊔ D.𝔪 • L)
    (hc : ∀ i, Cong X D.𝔪 (u i) (D.β i)) : L ∈ D.lats := by
  have h1 : L ≤ Lev.loc D.𝔪 X.Λ := by
    obtain ⟨s, hs, hN⟩ := Lev.nakayama hL.1 h
    intro v hv
    refine Lev.loc_loc hs (Submodule.span_le.2 ?_ (hN v hv))
    rintro _ ⟨i, rfl⟩
    have := add_mem (Lev.loc_mono Submodule.smul_le_right (Lev.cong_iff.1 (hc i)))
      (Lev.le_loc _ (D.β_mem i))
    rwa [sub_add_cancel] at this
  have h2 : X.Λ ≤ L ⊔ D.𝔪 • X.Λ := by
    refine D.β_span.trans (sup_le (Submodule.span_le.2 ?_) le_sup_right)
    rintro _ ⟨i, rfl⟩
    refine Lev.mem_of_loc (D.β_mem i) le_sup_right ?_
    have := add_mem (Lev.loc_mono (le_sup_right (a := L)) (Lev.cong_iff.1 (Lev.cong_symm (hc i))))
      (Lev.le_loc _ (Submodule.mem_sup_left (hu i)))
    rwa [sub_add_cancel] at this
  obtain ⟨s, hs, h1⟩ := Lev.exists_mul_of_fg hL.1 h1
  obtain ⟨t, ht, h2⟩ := Lev.nakayama X.Λ_fg h2
  have h1' (v) (hv : v ∈ L) : Lev.bar t • v ∈ X.Λ := (hΛ.2 _).2 fun y hy => by
    rw [Lev.EF_smul, Lev.bar_bar]
    exact (hL.2 _).1 hv _ (h2 y hy)
  have h2' (v) (hv : v ∈ X.Λ) : Lev.bar s • v ∈ L := (hL.2 _).2 fun y hy => by
    rw [Lev.EF_smul, Lev.bar_bar]
    exact (hΛ.2 _).1 hv _ (h1 y hy)
  obtain ⟨a, b, hab⟩ := Lev.cop_glue D.cop hs (Lev.cop_bar ht)
  obtain ⟨a', b', hab'⟩ := Lev.cop_glue D.cop ht (Lev.cop_bar hs)
  refine ⟨hL, _, Lev.cop_mul hab hab', fun v hv => ?_, fun v hv => ?_⟩
  · rw [mul_comm, mul_smul]
    refine X.Λ.smul_mem _ ?_
    rw [add_smul, mul_smul, mul_smul]
    exact add_mem (X.Λ.smul_mem _ (h1 v hv)) (X.Λ.smul_mem _ (h1' v hv))
  · rw [mul_smul]
    refine L.smul_mem _ ?_
    rw [add_smul, mul_smul, mul_smul]
    exact add_mem (L.smul_mem _ (h2 v hv)) (L.smul_mem _ (h2' v hv))

end GlobalTheory.Dict.Move

theorem GlobalTheory.Dict.exists_move_marked : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (D : SW.Level X) (L : Lt E r) (u : Fin r → Fin r → E), SelfD X X.Λ → SelfD X L → (∀ i, u i ∈ L) → L ≤ Submodule.span (𝓞 E) (Set.range u) ⊔ D.𝔪 • L → ∃ ga : GL (Fin r) E, IsUn X ga ∧ mapL ga L ∈ D.lats ∧ ∀ i, Cong X D.𝔪 ((ga : Matrix (Fin r) (Fin r) E) *ᵥ u i) (D.β i) := by
  intro E _ _ _ r X D L u hΛ hL hu h
  obtain ⟨ga, hun, hc⟩ := Move.exists_cong D hL h
  refine ⟨ga, hun, Move.mem_lats D (u := fun i => Lev.lin ga (u i)) hΛ (Lev.selfD_mapL hun hL)
    (fun i => ⟨_, hu i, rfl⟩) ?_ hc, hc⟩
  refine (Submodule.map_mono (f := Lev.lin ga) h).trans ?_
  rw [Submodule.map_sup, Submodule.map_span, ← Set.range_comp, Submodule.map_smul'']
  exact le_rfl
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict

namespace GlobalTheory.Dict.ProjProj

open GlobalTheory.SW.TensVac

theorem proj_proj_of_good {E : Type} [Field E] [NumberField E] [IsCMField E] {r g n : ℕ}
    {X : Data E r} {bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ} (idx : Fin g ≃ X.Ψ × Fin r)
    (hs : IsSympl X bas) (hn : Even n) {w : E}
    {A₁ A₂ A₃ : AddSubgroup (Matrix (Fin n) (Fin r) E)} (h₂ : Good X w A₂) (h₃ : Good X w A₃)
    (hle : A₂ ≤ (A₂ ⊓ A₁) ⊔ (A₂ ⊓ A₃)) {v : TF n g} (hv : IsVac X bas w A₁ v) :
    projA X bas w A₃ (projA X bas w A₂ v) = projA X bas w A₃ v := by
  obtain ⟨v₂, hv₂, -⟩ := h₂.vac hs
  obtain ⟨v₃, hv₃, -⟩ := h₃.vac hs
  have hsb₂ := (h₂.proj idx hs hn hv.1 hv₂).1
  rw [(h₃.proj idx hs hn hsb₂ hv₃).2, (h₃.proj idx hs hn hv.1 hv₃).2]
  congr 1
  have hfin := h₂.finite idx hs hn hv.1
  have hsb : ∀ ψ ∈ hfin.toFinset, IsSB ψ := by
    intro ψ hψ
    obtain ⟨y, -, rfl⟩ := hfin.mem_toFinset.1 hψ
    exact rho_sb idx hs hn y hv.1
  have hpos : (((fun y => epsW X w y • heisG X bas y v) '' A₂).ncard : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.2 ((Set.ncard_pos hfin).2 ⟨_, 0, A₂.zero_mem, rfl⟩).ne'
  obtain ⟨h1, h2⟩ := sum_sb_ip _ hsb hv₃.1
  rw [projA, finsum_mem_eq_finite_toFinset_sum _ hfin, ip_smul_left _ h1 hv₃.1, h2,
    Finset.sum_congr rfl (g := fun _ => SW.ip v v₃), Finset.sum_const,
    ← Set.ncard_eq_toFinset_card _ hfin, nsmul_eq_mul, inv_mul_cancel_left₀ hpos]
  intro ψ hψ
  obtain ⟨y, hy, rfl⟩ := hfin.mem_toFinset.1 hψ
  obtain ⟨a, ha, b, hb, rfl⟩ := AddSubgroup.mem_sup.1 (hle hy)
  show SW.ip (epsW X w (a + b) • heisG X bas (a + b) v) v₃ = SW.ip v v₃
  rw [add_comm a b, ← h₂.rho_rho idx hs hn hb.1 ha.1 hv.1, hv.2.2 a ha.2,
    ← rho_ip (w := w) idx hs hn b hv.1 hv₃.1, hv₃.2.2 b hb.2]

theorem proj_proj : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ w : E, IsIntegral ℤ w → w + cc w = 1 → ∀ L₁ L₂ L₃ : Lt E r, SelfD X L₁ → SelfD X L₂ → SelfD X L₃ → ∀ Λ₁ ∈ Vset E n 1, ∀ Λ₂ ∈ Vset E n 1, ∀ Λ₃ ∈ Vset E n 1, tens Λ₂ L₂ ≤ (tens Λ₂ L₂ ⊓ tens Λ₁ L₁) ⊔ (tens Λ₂ L₂ ⊓ tens Λ₃ L₃) → ∀ v : TF n g, IsVac X bas w (tens Λ₁ L₁) v → projA X bas w (tens Λ₃ L₃) (projA X bas w (tens Λ₂ L₂) v) = projA X bas w (tens Λ₃ L₃) v := by
  intro E _ _ _ r X g bas idx n hs hn w hw hw' L₁ L₂ L₃ _ hL₂ hL₃ Λ₁ _ Λ₂ hΛ₂ Λ₃ hΛ₃ hle v hv
  have good (L) (hL : SelfD X L) (Λ) (hΛ : Λ ∈ Vset E n 1) : Good X w (tens Λ L) := by
    obtain ⟨h1, h2, h3, -⟩ := GlobalTheory.T.tensorLattice_selfDual_semicharacter_index E r X g bas idx n hs hn w hw hw' L hL 1 Λ hΛ
    exact ⟨h1, h2, h3⟩
  exact proj_proj_of_good idx hs hn (good L₂ hL₂ Λ₂ hΛ₂) (good L₃ hL₃ Λ₃ hΛ₃) hle hv

end GlobalTheory.Dict.ProjProj
end
