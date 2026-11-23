module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PlacesOf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.PoincareConstantEq
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle049
import Formalism.LocalToGlobal.Columns.StdLatUnimodular
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.MaxMass
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle007
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle304
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsBoundedBasis
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle114
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle263
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle315
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle332
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle173
public import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle007
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsZEquivGramBoundedMinors
public import Formalism.SharpRestriction.CuspSpanNormBounds.CongruenceAtSplitFrobeniusHolds
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeanCountPrimitiveSublatticesOverGenus
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AtBase
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RowsConc

@[expose] public section

section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.HL

theorem GCoord.c_eq_one_of_gS_mem : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) {T T' : D.host.E} (F00 : LFlag (D.sp.Y 0) D.R.rS T) (F'0 : LFlag (D.sp.Y 0) D.R.rS T') (FP : ∀ p : PlF D, LocNG.FPair (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p) D.R.rS) (G : GFrames (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)) D.R.rS D.R.k) (c : GCoord (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) F00 F'0 FP G) (P : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.E)), ((_root_.Formalism.MainNotions.S.Lat.gS D : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal → G.c (below D P) = 1 := by
  intro D X Y T T' F00 F'0 FP G c P hP
  set p : PlF D := below D P with hp
  have hmem : ∀ n : ℕ, ((n : 𝓞 D.host.F) ∈ p.asIdeal ↔ ((n : 𝓞 D.host.E)) ∈ P.asIdeal) := by
    intro n
    show (n : 𝓞 D.host.F) ∈ Ideal.comap _ P.asIdeal ↔ _
    rw [Ideal.mem_comap, map_natCast]
  have hg : ∃ i, ((D.host.g i : ℕ) : 𝓞 D.host.F) ∈ p.asIdeal := by
    have h1 : ((_root_.Formalism.MainNotions.S.Lat.gS D : ℕ) : 𝓞 D.host.F) ∈ p.asIdeal := (hmem _).2 hP
    simp only [_root_.Formalism.MainNotions.S.Lat.gS, Nat.cast_mul] at h1
    rcases p.isPrime.mem_or_mem h1 with h | h
    · exact ⟨0, h⟩
    · exact ⟨1, h⟩
  obtain ⟨i, hi⟩ := hg
  have hchar : Loc.resChar p = D.host.g i := by
    have hz : ((D.host.g i : ℕ) : 𝓞 D.host.F ⧸ p.asIdeal) = 0 := by
      rw [← map_natCast (Ideal.Quotient.mk p.asIdeal), Ideal.Quotient.eq_zero_iff_mem]
      exact hi
    have hd : ringChar (𝓞 D.host.F ⧸ p.asIdeal) ∣ D.host.g i := ringChar.dvd hz
    exact (Nat.prime_dvd_prime_iff_eq (D.s.atP p).ellPrime.out (D.host.g_prime i)).1 hd
  have hgp : gpart p = D.host.g i := by
    have hne := D.host.g_ne
    fin_cases i
    · simp [gpart, hchar]
    · simp [gpart, hchar, Ne.symm hne]
  have hδ := Y.δ_pin p i hi
  have hne : ∀ j, ((D.host.g j : ℕ) : D.host.E) ≠ 0 := fun j => Nat.cast_ne_zero.2 (D.host.g_prime j).ne_zero
  have hneF : ∀ j, ((D.host.g j : ℕ) : D.host.F) ≠ 0 := fun j => Nat.cast_ne_zero.2 (D.host.g_prime j).ne_zero
  have key := c.c_eq p
  have hone : algebraMap (D.s.atP p).Fp (D.s.atP p).Ep ((G.c p).val) = algebraMap (D.s.atP p).Fp (D.s.atP p).Ep 1 := by
    rw [key]
    change algebraMap _ _ (Y.δ p) * _ = _
    rw [hδ, ← (D.s.atP p).compat, ← map_mul, map_one]
    have h1 : algebraMap D.host.F D.host.E ((D.host.g 0 : D.host.F) * D.host.g 1 / D.host.g i) *
        ((uP p : ℚ) : D.host.E) = 1 := by
      simp only [uP, hgp, _root_.Formalism.MainNotions.S.Lat.gS, map_div₀, map_mul, map_natCast]
      push_cast
      have := hne 0; have := hne 1; have := hne i
      field_simp
    rw [h1, map_one]
  haveI : Nontrivial (D.s.atP p).Ep :=
    Module.nontrivial_of_finrank_pos (R := (D.s.atP p).Fp) (by rw [(D.s.atP p).rank]; norm_num)
  have hv : ((G.c p).val : (D.s.atP p).Fp) = 1 :=
    (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep).injective hone
  exact Units.ext hv

end GlobalTheory.HL
end

section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.HL.ThetaG

open IsDedekindDomain

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E}

theorem mem_lat_span_smul_iff (A : Places F E sig) {n : ℕ} (p : HeightOneSpectrum (𝓞 F))
    (Λ : Submodule (𝓞 E) (Fin n → E)) (a : 𝓞 E) (x : Fin n → (A.loc p).Ep) :
    x ∈ A.lat p (Ideal.span {a} • Λ) ↔ ∃ z ∈ A.lat p Λ, x = (A.loc p).ιE (a : E) • z := by
  let φ : (Fin n → (A.loc p).Ep) →ₗ[(A.L p).O] (Fin n → (A.loc p).Ep) :=
    (LinearMap.lsmul (A.loc p).Ep (Fin n → (A.loc p).Ep) ((A.loc p).ιE (a : E))).restrictScalars (A.L p).O
  have hφ : ∀ v, φ v = (A.loc p).ιE (a : E) • v := fun v => rfl
  have hbc : ∀ v : Fin n → E, A.bc p (a • v) = φ (A.bc p v) := by
    intro v
    funext i
    show (A.loc p).ιE ((a : E) * v i) = (A.loc p).ιE (a : E) * (A.loc p).ιE (v i)
    exact map_mul _ _ _
  have hset : A.bc p '' ((Ideal.span {a} • Λ : Submodule (𝓞 E) (Fin n → E)) : Set (Fin n → E)) =
      φ '' (A.bc p '' (Λ : Set (Fin n → E))) := by
    rw [Submodule.ideal_span_singleton_smul, Submodule.coe_pointwise_smul, ← Set.image_smul,
      Set.image_image, Set.image_image]
    exact Set.image_congr fun v _ => hbc v
  have heq : A.lat p (Ideal.span {a} • Λ) = (A.lat p Λ).map φ := by
    unfold Places.lat
    rw [hset, Submodule.map_span]
  rw [heq, Submodule.mem_map]
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨z, hz, rfl⟩
  · rintro ⟨z, hz, rfl⟩
    exact ⟨z, hz, rfl⟩

theorem smul_mem_iff_of_unit {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] (O : Subring R)
    (N : Submodule O M) (θ s w b : R) (hw : w ∈ O) (hb : b ∈ O) (hs : s = θ * b) (hwb : w * b = 1) (x : M) :
    (∃ y ∈ N, x = θ • y) ↔ ∃ z ∈ N, x = s • z := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨(⟨w, hw⟩ : O) • y, N.smul_mem _ hy, ?_⟩
    rw [Subring.smul_def, smul_smul, hs, mul_assoc, mul_comm b w, hwb, mul_one]
  · rintro ⟨z, hz, rfl⟩
    refine ⟨(⟨b, hb⟩ : O) • z, N.smul_mem _ hz, ?_⟩
    rw [Subring.smul_def, smul_smul, hs]

theorem resChar_eq_of_mem (p : HeightOneSpectrum (𝓞 F)) {q : ℕ} (hq : q.Prime)
    (h : ((q : ℕ) : 𝓞 F) ∈ p.asIdeal) : Formalism.MainNotions.S.Loc.resChar p = q := by
  unfold Formalism.MainNotions.S.Loc.resChar
  haveI := p.isPrime
  have h0 : ((q : ℕ) : 𝓞 F ⧸ p.asIdeal) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk p.asIdeal)]
    exact Ideal.Quotient.eq_zero_iff_mem.2 h
  rcases hq.eq_one_or_self_of_dvd _ (ringChar.dvd h0) with h1 | h1
  · exact absurd h1 CharP.ringChar_ne_one
  · exact h1

end GlobalTheory.HL.ThetaG

namespace GlobalTheory.HL.ThetaG

open IsDedekindDomain ValuativeRel

theorem inTh_lat_iff : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) {T T' : D.host.E} (F00 : LFlag (D.sp.Y 0) D.R.rS T) (F'0 : LFlag (D.sp.Y 0) D.R.rS T') (FP : ∀ p : PlF D, LocNG.FPair (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p) D.R.rS) (G : GFrames (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)) D.R.rS D.R.k) (c : GCoord (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) F00 F'0 FP G) (P : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.E)), ((_root_.Formalism.MainNotions.S.Lat.gS D : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal → ∀ (Λ : G.Lt) (x : (G.S (below D P)).V), (G.S (below D P)).InTh ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).lat (below D P) Λ) x ↔ x ∈ (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).lat (below D P) (Ideal.span {((_root_.Formalism.MainNotions.S.Lat.gS D : ℕ) : 𝓞 D.host.E)} • Λ) := by
  intro D X Y T T' F00 F'0 FP G c P hP Λ x
  haveI := P.isPrime
  have hmem : ∀ i : Fin 2, ((D.host.g i : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal →
      Formalism.MainNotions.S.Loc.resChar (below D P) = D.host.g i := by
    intro i hi
    apply resChar_eq_of_mem (below D P) (D.host.g_prime i)
    change _ ∈ Ideal.comap _ P.asIdeal
    rw [Ideal.mem_comap, map_natCast]
    exact hi
  have hg : ((_root_.Formalism.MainNotions.S.Lat.gS D : ℕ) : 𝓞 D.host.E) =
      ((D.host.g 0 : ℕ) : 𝓞 D.host.E) * ((D.host.g 1 : ℕ) : 𝓞 D.host.E) := by
    unfold _root_.Formalism.MainNotions.S.Lat.gS
    push_cast
    ring
  obtain ⟨i, j, hij, hi, hgij⟩ : ∃ i j : Fin 2, D.host.g i ≠ D.host.g j ∧
      ((D.host.g i : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal ∧
      ((_root_.Formalism.MainNotions.S.Lat.gS D : ℕ) : 𝓞 D.host.E) = ((D.host.g i : ℕ) : 𝓞 D.host.E) * ((D.host.g j : ℕ) : 𝓞 D.host.E) := by
    rw [hg] at hP
    rcases P.isPrime.mem_or_mem hP with h | h
    · exact ⟨0, 1, D.host.g_ne, h, hg⟩
    · exact ⟨1, 0, D.host.g_ne.symm, h, by rw [hg, mul_comm]⟩
  have hres := hmem i hi
  have hj : ((D.host.g j : ℕ) : 𝓞 D.host.F) ∉ (below D P).asIdeal := by
    intro hj'
    exact hij (hres.symm.trans (resChar_eq_of_mem (below D P) (D.host.g_prime j) hj'))
  have hsome : ((D.s.atP (below D P)).split).isSome = true :=
    (D.s_split (below D P)).2 (by rw [hres]; fin_cases i <;> simp)
  obtain ⟨sg, hsg⟩ := Option.isSome_iff_exists.1 hsome
  have hA := (Y.agree (below D P)).2.2.2.2.2
  rw [hsg] at hA
  obtain ⟨g', hM, hq⟩ : ∃ g', (Y.M (below D P)).split = some g' ∧ g'.q = sg.q := by
    cases hM : (Y.M (below D P)).split with
    | none => rw [hM] at hA; exact hA.elim
    | some g' => rw [hM] at hA; exact ⟨g', rfl, hA.2⟩
  have hgg := (c.c (below D P)).gg_some g' hM
  have hth : (G.S (below D P)).th = ((D.host.g i : ℕ) : (D.s.atP (below D P)).Fp) := by
    unfold Frames.th
    rw [if_pos hgg.1, hgg.2, hq, sg.q_eq, hres]
  haveI := ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc (below D P)).char0
  have hgj0 : ((D.host.g j : ℕ) : ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc (below D P)).Fp) ≠ 0 :=
    Nat.cast_ne_zero.2 (D.host.g_prime j).ne_zero
  have hval : (below D P).valuation D.host.F ((D.host.g j : ℕ) : D.host.F) = 1 := by
    rw [← map_natCast (algebraMap (𝓞 D.host.F) D.host.F)]
    exact le_antisymm ((below D P).valuation_le_one _)
      (not_lt.1 fun hlt => hj (((below D P).valuation_lt_one_iff_mem (K := D.host.F) _).1 hlt))
  have hint : ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc (below D P)).ιF ((D.host.g j : ℕ) : D.host.F)⁻¹ ∈ 𝒪[((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc (below D P)).Fp] :=
    (GlobalTheory.HL.PlacesInt.mem_int_iff ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc (below D P)) _).2 (by rw [map_inv₀, hval, inv_one])
  have hιF : ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc (below D P)).ιF ((D.host.g j : ℕ) : D.host.F)⁻¹ =
      ((D.host.g j : ℕ) : ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc (below D P)).Fp)⁻¹ := by
    rw [map_inv₀, map_natCast]
  let w : ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc (below D P)).Ep :=
    algebraMap ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc (below D P)).Fp ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc (below D P)).Ep ((D.host.g j : ℕ) : ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc (below D P)).Fp)⁻¹
  have hwO : w ∈ ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).L (below D P)).O := by
    rw [hιF] at hint
    refine (((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).L (below D P)).O_def _).2 ?_
    have : IsIntegral 𝒪[((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc (below D P)).Fp]
        (algebraMap 𝒪[((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc (below D P)).Fp] ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc (below D P)).Ep ⟨_, hint⟩) :=
      isIntegral_algebraMap
    exact this
  have hw : w * ((D.host.g j : ℕ) : ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc (below D P)).Ep) = 1 := by
    simp only [w]
    rw [← map_natCast (algebraMap ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc (below D P)).Fp ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc (below D P)).Ep), ← map_mul,
      inv_mul_cancel₀ hgj0, map_one]
  have huO : ((D.host.g j : ℕ) : ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc (below D P)).Ep) ∈
      ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).L (below D P)).O :=
    natCast_mem _ _
  have hι : ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc (below D P)).ιE (((((D.host.g i : ℕ) : 𝓞 D.host.E) * ((D.host.g j : ℕ) : 𝓞 D.host.E) :
      𝓞 D.host.E)) : D.host.E) =
      ((D.host.g i : ℕ) : ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc (below D P)).Ep) * ((D.host.g j : ℕ) : ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc (below D P)).Ep) := by
    push_cast
    rw [map_mul, map_natCast, map_natCast]
  have hθE : algebraMap ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc (below D P)).Fp
      ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc (below D P)).Ep (G.S (below D P)).th =
      ((D.host.g i : ℕ) : ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc (below D P)).Ep) := by
    rw [hth]
    exact map_natCast _ _
  have hιS : ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc (below D P)).ιE ((((_root_.Formalism.MainNotions.S.Lat.gS D : ℕ) : 𝓞 D.host.E)) : D.host.E) =
      ((D.host.g i : ℕ) : ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc (below D P)).Ep) *
        ((D.host.g j : ℕ) : ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc (below D P)).Ep) := by
    rw [hgij]
    exact hι
  obtain ⟨a, ha⟩ : ∃ a : ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc (below D P)).Ep, ((D.host.g i : ℕ) : ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc (below D P)).Ep) = a := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc (below D P)).Ep, ((D.host.g j : ℕ) : ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc (below D P)).Ep) = b := ⟨_, rfl⟩
  rw [ha, hb] at hιS
  rw [ha] at hθE
  rw [hb] at hw huO
  clear_value w
  have hs : ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc (below D P)).ιE ((((_root_.Formalism.MainNotions.S.Lat.gS D : ℕ) : 𝓞 D.host.E)) : D.host.E) =
      algebraMap ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc (below D P)).Fp
        ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc (below D P)).Ep (G.S (below D P)).th * b := by
    rw [hιS, hθE]
  unfold Frames.InTh
  rw [mem_lat_span_smul_iff]
  exact smul_mem_iff_of_unit _ _ _ _ w b hwO huO hs hw x

end GlobalTheory.HL.ThetaG
end
end

section

open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.DegCnt.PrimGenus

section
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]

theorem nondeg_of_pd (h : V →ₗ⋆[K] V →ₗ[K] K) (hp : GlobalTheory.Mass.PD h) : h.Nondegenerate := by
  unfold GlobalTheory.Mass.PD at hp
  have key : ∀ x, h x x = 0 → x = 0 := by
    intro x hx
    by_contra hne
    have hlt := hp (Classical.arbitrary (K →+* ℂ)) x hne
    rw [hx, map_zero, Complex.zero_re] at hlt
    exact lt_irrefl _ hlt
  constructor
  · intro x hx
    exact key x (hx x)
  · intro y hy
    exact key y (hy y)

end

theorem gen_of_cyclic {R W : Type} [CommRing R] [AddCommGroup W] [Module R W] {A B : Submodule R W} (hle : B ≤ A)
    (I : Ideal R) (e : (↥A ⧸ B.comap A.subtype) ≃ₗ[R] (R ⧸ I)) :
    ∃ t : Finset W, t.card ≤ 1 ∧ A = B ⊔ Submodule.span R (t : Set W) := by
  obtain ⟨a, ha⟩ := Submodule.Quotient.mk_surjective _ (e.symm (Ideal.Quotient.mk I 1))
  refine ⟨{(a : W)}, by simp, le_antisymm ?_ ?_⟩
  · intro x hx
    obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (e (Submodule.Quotient.mk ⟨x, hx⟩))
    have hmk : Ideal.Quotient.mk I r = r • Ideal.Quotient.mk I 1 := by
      rw [Algebra.smul_def, map_one, mul_one]
      rfl
    have h1 : Submodule.Quotient.mk (⟨x, hx⟩ : A) = Submodule.Quotient.mk (p := B.comap A.subtype) (r • a) := by
      rw [Submodule.Quotient.mk_smul, ha, ← LinearEquiv.map_smul, ← hmk, hr, LinearEquiv.symm_apply_apply]
    rw [Submodule.Quotient.eq] at h1
    have h2 : x - r • (a : W) ∈ B := by simpa using h1
    have h3 : x = (x - r • (a : W)) + r • (a : W) := by abel
    rw [h3]
    exact Submodule.add_mem_sup h2 (Submodule.smul_mem _ r (Submodule.subset_span (by simp)))
  · exact sup_le hle (Submodule.span_le.mpr (by simp [a.2]))

theorem exponents (n D k s l : ℝ) (hn : 1 ≤ n) (hD : 1 ≤ D) (hs : 0 ≤ s) :
    n ^ ((k - s) / 2) * (n * D) ^ ((9 * s + 8 + 4 * l) / 2) ≤
      D ^ ((k - 1) / 2) * ((n / D) ^ (k / 2) * (n * D) ^ (5 * s + 5 + 2 * (1 + l))) := by
  have hn0 : 0 < n := by linarith
  have hD0 : 0 < D := by linarith
  have ha : 0 ≤ Real.log n := Real.log_nonneg hn
  have hb : 0 ≤ Real.log D := Real.log_nonneg hD
  simp only [Real.rpow_def_of_pos hn0, Real.rpow_def_of_pos hD0, Real.rpow_def_of_pos (mul_pos hn0 hD0),
    Real.rpow_def_of_pos (div_pos hn0 hD0), Real.log_mul hn0.ne' hD0.ne', Real.log_div hn0.ne' hD0.ne',
    ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith [mul_nonneg ha hs, mul_nonneg hb hs]

private theorem finrank_eq_two_mul_fDeg (K : Type) [Field K] [NumberField K] [StarRing K] (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) :
    Module.finrank ℚ K = 2 * Formalism.HermitianLatticesTheory.fDeg K := by
  haveI := hK.1
  rw [IsTotallyComplex.finrank]
  unfold Formalism.HermitianLatticesTheory.fDeg
  rw [NumberField.InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces, IsTotallyComplex.nrRealPlaces_eq_zero,
    zero_add]

private theorem mass_bound_rpow_le (K : Type) [Field K] [NumberField K] [StarRing K] (hK : Formalism.HermitianLatticesTheory.IsCMUnram K)
    (hv : 1 ≤ Formalism.HermitianLatticesTheory.vInv K) :
    1 ≤ (20 * ((Formalism.HermitianLatticesTheory.fDeg K) : ℝ) * (2 * Formalism.HermitianLatticesTheory.vInv K) ^ 2) ^ (2 * ((Formalism.HermitianLatticesTheory.fDeg K) : ℝ) * (6 + cf K)) ∧
    (20 * (Formalism.HermitianLatticesTheory.fDeg K : ℝ) * (2 * Formalism.HermitianLatticesTheory.vInv K) ^ 2) ^ (16 * Formalism.HermitianLatticesTheory.fDeg K) ≤
      (20 * ((Formalism.HermitianLatticesTheory.fDeg K) : ℝ) * (2 * Formalism.HermitianLatticesTheory.vInv K) ^ 2) ^ (2 * ((Formalism.HermitianLatticesTheory.fDeg K) : ℝ) * (6 + cf K)) := by
  have hd := finrank_eq_two_mul_fDeg K hK
  have hfpos : 0 < Formalism.HermitianLatticesTheory.fDeg K := by
    have : 0 < Module.finrank ℚ K := Module.finrank_pos
    omega
  have hf : (1 : ℝ) ≤ (Formalism.HermitianLatticesTheory.fDeg K : ℝ) := by exact_mod_cast hfpos
  have hB : 1 ≤ 20 * (Formalism.HermitianLatticesTheory.fDeg K : ℝ) * (2 * Formalism.HermitianLatticesTheory.vInv K) ^ 2 := by nlinarith
  have hd2 : (2 : ℝ) ≤ (Module.finrank ℚ K : ℝ) := by
    rw [hd]
    push_cast
    linarith
  have hl : 1 ≤ Real.logb 2 (Module.finrank ℚ K : ℝ) := by
    rw [Real.le_logb_iff_rpow_le (by norm_num) (by linarith)]
    simpa using hd2
  have hcf : 2 ≤ cf K := by
    unfold cf
    linarith
  refine ⟨Real.one_le_rpow hB (by nlinarith), ?_⟩
  rw [← Real.rpow_natCast]
  apply Real.rpow_le_rpow_of_exponent_le hB
  push_cast
  nlinarith

private theorem laurent_T_unit_zpow_eq_T (T : ℝ) (hT : 2 ≤ T) (k f : ℕ) (hk : 1 ≤ k) :
    (T ^ (2 * f)) ^ (((k : ℝ) - 1) / 2) ≤ ((T ^ k - 1) / (T - 1)) ^ f := by
  have hT0 : 0 ≤ T := by linarith
  have h1 : (T ^ (2 * f)) ^ (((k : ℝ) - 1) / 2) = (T ^ (k - 1)) ^ f := by
    rw [← Real.rpow_natCast T (2 * f), ← Real.rpow_mul hT0, ← pow_mul, ← Real.rpow_natCast]
    congr 1
    push_cast [Nat.cast_sub hk]
    ring
  rw [h1]
  apply pow_le_pow_left₀ (pow_nonneg hT0 _)
  rw [le_div_iff₀ (by linarith)]
  have h2 : (1 : ℝ) ≤ T ^ (k - 1) := one_le_pow₀ (by linarith)
  have h3 : T ^ k = T ^ (k - 1) * T := by
    rw [← pow_succ]
    congr 1
    omega
  rw [h3]
  nlinarith

private theorem le_dual_of_integral_form {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
    [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule (𝓞 K) V)
    (hi : ∀ x ∈ L, ∀ y ∈ L, h x y ∈ (1 : Submodule (𝓞 K) K)) : L ≤ Formalism.HermitianLatticesTheory.dual h L := by
  intro x hx
  simp only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf]
  intro y hy
  first
  | exact hi x hx y hy
  | exact hi y hy x hx
  | simpa using hi x hx y hy
  | simpa using hi y hy x hx

private theorem norm_cofactor_le_of_factorization {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
    [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (h : V →ₗ⋆[K] V →ₗ[K] K)
    (L : Submodule (𝓞 K) V) (T : ℕ)
    (e : (↥(Formalism.HermitianLatticesTheory.dual h L) ⧸ L.comap (Formalism.HermitianLatticesTheory.dual h L).subtype) ≃ₗ[𝓞 K] (𝓞 K ⧸ Ideal.span {(T : 𝓞 K)})) :
    GlobalTheory.Mass.discN h L = T ^ (2 * Formalism.HermitianLatticesTheory.fDeg K) := by
  have hc : GlobalTheory.Mass.discN h L = Nat.card (𝓞 K ⧸ Ideal.span {(T : 𝓞 K)}) := by
    unfold GlobalTheory.Mass.discN GlobalTheory.Mass.idxN AddSubgroup.relIndex AddSubgroup.index
    exact Nat.card_congr e.toEquiv
  rw [hc, ← Submodule.cardQuot_apply, ← Ideal.absNorm_apply, Ideal.absNorm_span_singleton]
  have hT : ((T : 𝓞 K)) = algebraMap ℤ (𝓞 K) (T : ℤ) := by simp
  rw [hT, Algebra.norm_algebraMap, NumberField.RingOfIntegers.rank, finrank_eq_two_mul_fDeg K hK]
  simp [Int.natAbs_pow]

private theorem mul_mul_mul_le_of_bounds (A Bm X Y C R Q1 Q2 G mk : ℝ) (h10 : Bm * A ≤ mk * C) (hexp : X * Y ≤ R * (Q1 * Q2))
    (htp : R ≤ G) (hXY : 0 ≤ X * Y) (hkC : 0 ≤ mk * C) (hQ : 0 ≤ Q1 * Q2) :
    A * Bm * X * Y ≤ mk * G * C * Q1 * Q2 := by
  calc A * Bm * X * Y = (Bm * A) * (X * Y) := by ring
    _ ≤ (mk * C) * (R * (Q1 * Q2)) := mul_le_mul h10 hexp hXY hkC
    _ ≤ (mk * C) * (G * (Q1 * Q2)) := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right htp hQ) hkC
    _ = mk * G * C * Q1 * Q2 := by ring

theorem main : GlobalTheory.Mass.MaxMass → Formalism.HermitianLatticesTheory.SiegelMassRatio → ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → HasOrtho K → 1 ≤ Formalism.HermitianLatticesTheory.vInv K → GlobalTheory.Mass.PD H.B.flip → 3 ≤ (Module.finrank K V) → ∀ (T : ℕ) (L₀ : Submodule (𝓞 K) V) (Mb : ℝ), T.Prime → (∀ P : Ideal (𝓞 K), P.IsMaximal → (T : 𝓞 K) ∈ P → Ideal.absNorm P = T ∧ (T : 𝓞 K) ∉ P ^ 2) → GlobalTheory.Mass.IsIntLat H.B.flip L₀ → Nonempty ((↥(Formalism.HermitianLatticesTheory.dual H.B.flip L₀) ⧸ L₀.comap (Formalism.HermitianLatticesTheory.dual H.B.flip L₀).subtype) ≃ₗ[𝓞 K] (𝓞 K ⧸ Ideal.span {(T : 𝓞 K)})) → Mb = (20 * ((Formalism.HermitianLatticesTheory.fDeg K) : ℝ) * (2 * Formalism.HermitianLatticesTheory.vInv K) ^ 2) ^ (2 * ((Formalism.HermitianLatticesTheory.fDeg K) : ℝ) * (6 + cf K)) → ∀ D₀ : ℝ, D₀ = (T : ℝ) ^ (2 * (Formalism.HermitianLatticesTheory.fDeg K)) → ∀ s n : ℕ, 1 ≤ s → s < (Module.finrank K V) → 1 ≤ n → GlobalTheory.Mass.orbSum (Formalism.HermitianLatticesTheory.isom H.B.flip) (Formalism.HermitianLatticesTheory.genus H.B.flip L₀) (fun L => (((GlobalTheory.Mass.primSp H.B.flip L ((Module.finrank K V) - s) n).encard : ℕ∞) : ℝ≥0∞)) ≤ ENNReal.ofReal (Formalism.HermitianLatticesTheory.mass H.B.flip L₀ * (Mb * (2 * Formalism.HermitianLatticesTheory.vInv K) ^ (Formalism.HermitianLatticesTheory.fDeg K) * 16 ^ (s * (Module.finrank K V) * (Formalism.HermitianLatticesTheory.fDeg K))) * ((n : ℝ) / D₀) ^ (((Module.finrank K V) : ℝ) / 2) * ((n : ℝ) * D₀) ^ (5 * (s : ℝ) + 5 + 2 * cf K)) := by
  intro hMax hS K V _ _ _ _ _ _ _ _ H hK hO hv hPD hk T L₀ Mb hT hTP hL₀ hq hMb D₀ hD₀ s n hs hsk hn
  obtain ⟨ms, hms0, hms⟩ := GlobalTheory.OrthoMass.main K hK
  have hsymm : H.B.flip.IsSymm := GlobalTheory.HermLat.flip_isSymm H
  have hnd : H.B.flip.Nondegenerate := nondeg_of_pd H.B.flip hPD
  have hgen := GlobalTheory.T.cyclicDiscriminant_lattices_form_one_genus K V H.B.flip hK hsymm hnd T hT hTP
  obtain ⟨-, -, hstab, -⟩ := GlobalTheory.T.hermitianGenusMass_eq_orbitStabilizerMass K V H.B.flip hK hsymm hPD L₀ hL₀.1
  have hsk' : Module.finrank K V - s + s = Module.finrank K V := Nat.sub_add_cancel hsk.le
  have key := GlobalTheory.T.primitiveSublattice_mean_count_bound hMax K V H.B.flip hK hsymm hPD hO (Module.finrank K V - s) s (by omega) hs hsk'
    (Fin (Module.finrank K V - s) → K) (Formalism.HermitianLatticesTheory.massTelescope_form K _) (Formalism.HermitianLatticesTheory.massTelescope_lat K _)
    (Formalism.HermitianLatticesTheory.massTelescope_symm K _) (Formalism.HermitianLatticesTheory.massTelescope_ortho K _)
    (Fin s → K) (Formalism.HermitianLatticesTheory.massTelescope_form K s) (Formalism.HermitianLatticesTheory.massTelescope_lat K s)
    (Formalism.HermitianLatticesTheory.massTelescope_symm K s) (Formalism.HermitianLatticesTheory.massTelescope_ortho K s)
    n (T ^ (2 * Formalism.HermitianLatticesTheory.fDeg K)) hn (Nat.one_le_pow _ _ hT.pos)
    (Formalism.HermitianLatticesTheory.genus H.B.flip L₀) hstab (fun L hL => by
      obtain ⟨hLi, ⟨eL⟩⟩ := (hgen.2 L₀ L hL₀ hq).mp hL
      exact ⟨hLi, norm_cofactor_le_of_factorization hK H.B.flip L T eL, gen_of_cyclic (le_dual_of_integral_form H.B.flip L hLi.2) _ eL⟩)
  have hm : ∀ j, Formalism.HermitianLatticesTheory.mass (Formalism.HermitianLatticesTheory.massTelescope_form K j) (Formalism.HermitianLatticesTheory.massTelescope_lat K j) = ms j :=
    fun j => hms j _ _ _ (Formalism.HermitianLatticesTheory.massTelescope_symm K j) (Formalism.HermitianLatticesTheory.massTelescope_ortho K j)
  rw [hm, hm] at key
  have hmass := GlobalTheory.T.mass_genus_cyclicDiscriminant_splitPrime hMax K V H.B.flip hK hsymm hPD (by omega) (Fin (Module.finrank K V) → K)
    (Formalism.HermitianLatticesTheory.massTelescope_form K _) (Formalism.HermitianLatticesTheory.massTelescope_symm K _) (Formalism.HermitianLatticesTheory.massTelescope_lat K _)
    (Formalism.HermitianLatticesTheory.massTelescope_ortho K _) T hT hTP L₀ hL₀ hq
  rw [hm] at hmass
  obtain ⟨hMb1, hMbB⟩ := mass_bound_rpow_le K hK hv
  rw [← hMb] at hMb1 hMbB
  have hsmall : ∀ j, 1 ≤ j → j ≤ 2 → ms j ≤ Mb := fun j h1 h2 => by
    rw [← hm j]
    exact (GlobalTheory.SmallRankMass.mass_small hK hv h1 h2).trans hMbB
  have h10 := GlobalTheory.T.unimodularHermitianMass_mul_le_mass hS K hK hv (Module.finrank K V) s Mb ms hk hs hsk hms
    (hsmall 1 le_rfl (by norm_num)) (hsmall 2 (by norm_num) le_rfl) hMb1
  have hexp := exponents (n : ℝ) ((T : ℝ) ^ (2 * Formalism.HermitianLatticesTheory.fDeg K)) (Module.finrank K V : ℝ) (s : ℝ)
    (Real.logb 2 (Module.finrank ℚ K)) (by exact_mod_cast hn) (one_le_pow₀ (by exact_mod_cast hT.one_lt.le))
    (by positivity)
  have htp := laurent_T_unit_zpow_eq_T (T : ℝ) (by exact_mod_cast hT.two_le) (Module.finrank K V) (Formalism.HermitianLatticesTheory.fDeg K) (by omega)
  have hC : 0 ≤ Mb * (2 * Formalism.HermitianLatticesTheory.vInv K) ^ (Formalism.HermitianLatticesTheory.fDeg K) * 16 ^ (s * (Module.finrank K V) * (Formalism.HermitianLatticesTheory.fDeg K)) :=
    mul_nonneg (mul_nonneg (by linarith) (pow_nonneg (by linarith) _)) (by positivity)
  subst hD₀
  refine key.trans (ENNReal.ofReal_le_ofReal ?_)
  rw [hmass, Nat.cast_sub hsk.le, Nat.cast_pow]
  exact mul_mul_mul_le_of_bounds _ _ _ _ _ _ _ _ _ _ h10 hexp htp (by positivity) (mul_nonneg (hms0 _).le hC) (by positivity)

end GlobalTheory.DegCnt.PrimGenus
end

section

open NumberField Module Matrix Formalism.MainNotions.S Formalism.MainNotions.S.Lat
open scoped Classical

theorem _root_.GlobalTheory.T.exists_zEquiv_gram_bounded_minors : ∀ (K : Type) [Field K] [NumberField K], (∀ w : InfinitePlace K, w.IsComplex) → ∀ (r : ℕ) (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) K) (p : Point K (r + 1)), IsInCell (ZhatOM Z) p → ∃ Z₂ : Matrix (Fin (r + 1)) (Fin (r + 1)) K, ZEquiv Z Z₂ ∧ ∀ (τ : K →+* ℂ) (t : ℕ) (I J : Fin t → Fin (r + 1)), ‖τ (Z₂.submatrix I J).det‖ ≤ 4 ^ (r + 1) * (((r + 1).factorial : ℕ) : ℝ) ^ 2 * (Real.sqrt (finrank ℚ K) * |(discr K : ℝ)| ^ (1 / (finrank ℚ K : ℝ))) ^ (2 * (r + 1)) * ∏ l ∈ Finset.Icc 1 (r + 1), (max 1 ‖τ (leadMinorE Z l)‖ * max 1 ‖τ (leadMinorE Z l)‖⁻¹) := by
  first | exact @GlobalTheory.ReducedGram.exists_reduced | exact GlobalTheory.ReducedGram.exists_reduced | (intros; apply GlobalTheory.ReducedGram.exists_reduced <;> assumption)
end

section

open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory Formalism.BasicNotions Formalism.MainNotions.S
open scoped ENNReal Classical

theorem _root_.GlobalTheory.T.mean_count_primitive_sublattices_over_genus : ∀ c₀ : ℝ, 0 < c₀ → ∃ C₀ : ℝ, ∀ C : ℝ, C₀ ≤ C → ∀ (D : D7) (large₂ : SizeData₂ D) (u u' : D.what₂.Word) (C' Cl Cg cb Cu cT CT C0 A : ℝ), c₀ ≤ Cl → UnitaryVolumeMass.congruence_at_split_frobenius_holds D large₂ u u' C' Cl Cg cb Cu cT CT C0 A C := by
  first | exact @GlobalTheory.Mass.PrimMeanRow.main | exact GlobalTheory.Mass.PrimMeanRow.main | (intros; apply GlobalTheory.Mass.PrimMeanRow.main <;> assumption)
end
