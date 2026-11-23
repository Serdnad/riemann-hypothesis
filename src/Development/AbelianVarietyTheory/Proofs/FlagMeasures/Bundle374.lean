module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.RealObj
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.TermTieOf
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle360
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AtBase
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PlacesOf
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle077
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle364
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle358
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle348
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle347
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle066
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle362
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RowsConc
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SatGram
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.CorankRelation
public import Formalism.SharpRestriction.CuspSpanNormBounds.CntPartners
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle351
public import Formalism.UnipotentAdelicQuotients.Bundle003
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.SameKindIsometric
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle350
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.OneVectorCcOfSiegelWeil
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SiegelMeanCcOfOneVectorCc
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle240
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.Linter.Style
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
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.LoopTieOf
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle018
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle006

@[expose] public section

section

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf Formalism.L2.SG.LoopTieOf
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Matrix

theorem _root_.GlobalTheory.T.rationalFrameGram_embed_eq_realFrameGram : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (W : WittDat X) (u u' : D.what₂.Word) (s : TT Y u u') (τ : D.what₂.Tau), (ZhatL (lf D (FlagOfWord W u)) (Formalism.L2.SG.Saturated.mapL (W.δ u) (W.isom u) s.frame)).map (embS D τ) = Formalism.L2.SG.RealObj.ZX X u u' 1 s.pt.1 (X.pl.symm τ) := by
  first | exact @GlobalTheory.zhatRat_embed | exact GlobalTheory.zhatRat_embed | (intros; apply GlobalTheory.zhatRat_embed <;> assumption)
end

section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.FourierDecayAlt Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.SnFam
open scoped Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SnFam.CvScal

variable {D : D7}

lemma mem_orth_iff' {U : Submodule D.host.E (VS D).V} {y : (VS D).V} :
    y ∈ orth (VS D) U ↔ ∀ x ∈ U, (VS D).hT x y = 0 := by
  simp [orth, Submodule.mem_iInf]

lemma orth_anti {U U' : Submodule D.host.E (VS D).V} (h : U ≤ U') : orth (VS D) U' ≤ orth (VS D) U := by
  intro y hy
  rw [mem_orth_iff'] at hy ⊢
  exact fun x hx => hy x (h hx)

lemma z_mem_orth {T : D.host.E} (F : LFlag (D.sp.Y 0) D.R.rS T) : F.fl.z ∈ orth (VS D) (Xsp F) := by
  rw [mem_orth_iff']
  intro x hx
  have hx' : x ∈ Submodule.span D.host.E (Set.range F.fl.e) := hx
  clear hx
  induction hx' using Submodule.span_induction with
  | mem x h => obtain ⟨a, rfl⟩ := h; exact F.fl.z_orth a
  | zero => simp
  | add x y _ _ hx hy => simp [hx, hy]
  | smul c x _ hx => simp [hx]

lemma Xsp_le_Xplus {T : D.host.E} (F : LFlag (D.sp.Y 0) D.R.rS T) : Xsp F ≤ Xplus F := by
  show F.fl.X ≤ F.fl.X ⊔ _
  exact le_sup_left

lemma Xa_of_ge {T : D.host.E} (F : LFlag (D.sp.Y 0) D.R.rS T) {j : ℕ} (h : D.R.rS ≤ j) :
    Xflag F j = Xsp F := by
  show F.fl.Xa j = F.fl.X
  unfold FlagG.Xa FlagG.X
  congr 1
  ext v
  simp only [Set.mem_image, Set.mem_setOf_eq, Set.mem_range]
  constructor
  · rintro ⟨i, -, rfl⟩; exact ⟨i, rfl⟩
  · rintro ⟨i, rfl⟩; exact ⟨i, lt_of_lt_of_le i.2 h, rfl⟩

lemma nrat_mapsTo {T : D.host.E} {F : LFlag (D.sp.Y 0) D.R.rS T} {n} (hn : n ∈ NRat F) :
    ∀ x ∈ Xsp F, n x ∈ Xsp F := by
  intro x hx
  have h1 := hn.2.1 D.R.rS x (by rw [Xa_of_ge F (Nat.le_succ _)]; exact hx)
  rw [Xa_of_ge F le_rfl] at h1
  simpa using add_mem h1 hx

lemma map_eq_self {U : Submodule D.host.E (VS D).V} [FiniteDimensional D.host.E U]
    (f : (VS D).V ≃ₗ[D.host.E] (VS D).V) (h : ∀ x ∈ U, f x ∈ U) :
    U.map (f : (VS D).V →ₗ[D.host.E] (VS D).V) = U :=
  Submodule.eq_of_le_of_finrank_eq (by rintro _ ⟨x, hx, rfl⟩; exact h x hx) (LinearEquiv.finrank_map_eq f U)

lemma fd_Xsp {T : D.host.E} (F : LFlag (D.sp.Y 0) D.R.rS T) : FiniteDimensional D.host.E (Xsp F) :=
  FiniteDimensional.span_of_finite _ (Set.finite_range _)

lemma nrat_map {T : D.host.E} {F : LFlag (D.sp.Y 0) D.R.rS T} {n} (hn : n ∈ NRat F) :
    (Xsp F).map (n : (VS D).V →ₗ[D.host.E] (VS D).V) = Xsp F :=
  haveI := fd_Xsp F
  map_eq_self n (nrat_mapsTo hn)

lemma sgRel_iff {T T' : D.host.E} (F : LFlag (D.sp.Y 0) D.R.rS T) (F' : LFlag (D.sp.Y 0) D.R.rS T')
    (y y' : (VS D).V) (al al' : D.host.E) :
    SgRel F F' y y' al al' ↔ y - y' - (al • F.zt + al' • F'.zt) ∈ Xsp F ⊔ Xsp F' := by
  rw [Submodule.mem_sup]
  unfold SgRel
  constructor
  · rintro ⟨x, hx, x', hx', h⟩; exact ⟨x, hx, x', hx', by rw [h]; abel⟩
  · rintro ⟨x, hx, x', hx', h⟩
    refine ⟨x, hx, x', hx', ?_⟩
    have : y - y' = x + x' + (al • F.zt + al' • F'.zt) := by rw [h]; abel
    rw [this]; abel

end GlobalTheory.SnFam.CvScal

namespace GlobalTheory.SnFam.CvScal
variable {D : D7}

theorem pair_scalar (D : D7) {T T' : D.host.E} (Λ : Submodule (𝓞 D.host.E) (VS D).V) (F : LFlag (D.sp.Y 0) D.R.rS T)
    (F' F'' : LFlag (D.sp.Y 0) D.R.rS T') (_hΛ : Submodule.IsLattice D.host.E Λ) (hF : F.zt = F.fl.z)
    (hF' : F'.zt = F'.fl.z) (hF'' : F''.zt = F''.fl.z) (n) (hn : n ∈ NRat F) (m) (hm : m ∈ NRat F')
    (hfr : ∀ a, frame F'' a = (n * m) (frame F' a)) : IsScalar Λ F F' F'' (n * m) := by
  have hnm : ∀ v, (n * m) v = n (m v) := fun v => rfl
  have he : ∀ a, F''.fl.e a = n (m (F'.fl.e a)) := by
    intro a
    have := hfr (Fin.castSucc a)
    simpa [frame, FlagG.fvec, Fin.snoc_castSucc, hnm] using this
  have hz : F''.fl.z = n (m F'.fl.z) := by
    have := hfr (Fin.last _)
    simpa [frame, FlagG.fvec, Fin.snoc_last, hnm] using this

  have hX'' : Xsp F'' = (Xsp F').map (n : (VS D).V →ₗ[D.host.E] (VS D).V) := by
    have h1 : Xsp F'' = (Xsp F').map ((n : (VS D).V →ₗ[D.host.E] (VS D).V) ∘ₗ (m : (VS D).V →ₗ[D.host.E] (VS D).V)) := by
      show Submodule.span _ _ = Submodule.map _ (Submodule.span _ _)
      rw [Submodule.map_span, ← Set.range_comp]
      congr 2
      funext a
      exact he a
    rw [h1, Submodule.map_comp, nrat_map hm]
  have hsup : (Xsp F ⊔ Xsp F').map (n : (VS D).V →ₗ[D.host.E] (VS D).V) = Xsp F ⊔ Xsp F'' := by
    rw [Submodule.map_sup, nrat_map hn, hX'']
  have nX' : ∀ v ∈ Xsp F', n v ∈ Xsp F'' := fun v hv => hX'' ▸ Submodule.mem_map_of_mem hv
  intro y1 hy1 y2 _ y1' hy1' y2'' _ h12 h12' al al'
  rw [sgRel_iff, sgRel_iff, hF, hF', hF'']
  have oy1 : y1 ∈ orth (VS D) (Xsp F) := orth_anti (Xsp_le_Xplus F) hy1.2
  have oy1' : y1' ∈ orth (VS D) (Xsp F') := orth_anti (Xsp_le_Xplus F') hy1'.2
  have A : y2 - n y1 ∈ Xsp F := by
    have := add_mem h12 (hn.2.2 y1 oy1)
    rw [← neg_mem_iff]; convert this using 1; abel
  have B : y2'' - n y1' ∈ Xsp F'' := by
    have := add_mem h12' (nX' _ (hm.2.2 y1' oy1'))
    convert this using 1; rw [hnm, map_sub]; abel
  have C : F.fl.z - n F.fl.z ∈ Xsp F := by
    have := hn.2.2 _ (z_mem_orth F)
    rw [← neg_mem_iff]; convert this using 1; abel
  have Dd : F''.fl.z - n F'.fl.z ∈ Xsp F'' := by
    have := nX' _ (hm.2.2 _ (z_mem_orth F'))
    convert this using 1; rw [hz, map_sub]
  set d1 := y1 - y1' - (al • F.fl.z + al' • F'.fl.z) with hd1
  set d2 := y2 - y2'' - (al • F.fl.z + al' • F''.fl.z) with hd2
  have key : d2 = n d1 + ((y2 - n y1) - (y2'' - n y1') - al • (F.fl.z - n F.fl.z) - al' • (F''.fl.z - n F'.fl.z)) := by
    simp only [hd1, hd2, map_sub, map_add (f := _), map_smul, smul_sub]; abel
  have kmem : (y2 - n y1) - (y2'' - n y1') - al • (F.fl.z - n F.fl.z) - al' • (F''.fl.z - n F'.fl.z) ∈ Xsp F ⊔ Xsp F'' :=
    sub_mem (sub_mem (sub_mem (Submodule.mem_sup_left A) (Submodule.mem_sup_right B))
      (Submodule.smul_mem _ _ (Submodule.mem_sup_left C))) (Submodule.smul_mem _ _ (Submodule.mem_sup_right Dd))
  rw [key, Submodule.add_mem_iff_left _ kmem, ← hsup]
  constructor
  · intro h; exact Submodule.mem_map_of_mem h
  · rintro ⟨w, hw, hw'⟩
    have : w = d1 := n.injective hw'
    exact this ▸ hw

end GlobalTheory.SnFam.CvScal
end
end

section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.HL.LocCong

theorem bc_sum {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E}
    (A : GlobalTheory.HL.Places F E sig) {N r : ℕ} (p : IsDedekindDomain.HeightOneSpectrum (𝓞 F))
    (B : Fin (r + 1) → E) (v : Fin (r + 1) → Fin N → E) :
    A.bc p (∑ a, B a • v a) = ∑ a, (A.loc p).ιE (B a) • A.bc p (v a) := by
  funext i

  simp [GlobalTheory.HL.Places.bc, Finset.sum_apply, map_sum, smul_eq_mul]

theorem loc_cong : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), Formalism.MainNotions.S.Cnt.Stand D u u' → 4 * D.R.rS + 7 ≤ D.R.k → ∀ (w : Point D.host.E (D.R.rS + 1)) (F00 : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F'0 : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (FP : ∀ p : PlF D, LocNG.FPair (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p) D.R.rS), ZhatOM (ZhatL F00 F'0) = ptMat w → Gval F00 F'0 ≠ 0 → (∀ p, AtBase (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p F00 F'0 (Tu D u) (Tu D u') (FP p) ∧ (FP p).RelG (LocNG.theta (Y.M p))) → ∀ (G : GFrames (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)) D.R.rS D.R.k) (c : GCoord (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) F00 F'0 FP G), ∀ (t₀ : TauC Y u u') (ρ : ((VS D).V ≃ₗ[D.host.E] (VS D).V)) (U U' : Formalism.L2.SG.PairVal.MatR D), MovesTo F00 F'0 (lf D (X.Fu u)) t₀.frame ρ U U' → ∀ n m, n ∈ NRat (lf D (X.Fu u)) → m ∈ NRat (lf D (X.Fu u')) → Formalism.HermitianLatticesTheory.gmap (n⁻¹ * t₀.lin * m) t₀.lam' = t₀.lam → (∃ d, G.IsTerm d (c.lat (ρ * n) t₀.lam)) → ∀ P : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.E), ((_root_.Formalism.MainNotions.S.Lat.gS D : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal → ∃ ξ : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (𝓞 D.host.E), (∀ a b, b < a → ξ a b = 0) ∧ (∀ a, ξ a a = 1) ∧ ∀ b, frame (mapLF (n⁻¹ * t₀.lin * m) (lf D (X.Fu u'))) b - frameAct (frame (lf D (X.Fu u))) ξ b ∈ (haveI := P.isPrime; Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (Ideal.span {((_root_.Formalism.MainNotions.S.Lat.gS D : ℕ) : 𝓞 D.host.E)} • t₀.lam)) := by
  intro D X Y u u' hSt hk w F00 F'0 FP hZ hG hFP G c t₀ ρ U U' hMov n m hn hm hgm hterm P hP
  obtain ⟨d, hlat, hloc⟩ := hterm
  obtain ⟨B, B', hB1, hB2, hB1', hB2', hBB⟩ := GlobalTheory.T.moves_to_gives_integral_matrices D X Y u u' F00 F'0 t₀ ρ U U' hMov n m hn hm
  have hc1 := GlobalTheory.T.localScalar_eq_one_at_place_over_typePrimes D X Y F00 F'0 FP G c P hP
  have hSf : ∀ a, (G.S (below D P)).f a = (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).bc (below D P) (G.f a) := by
    intro a
    have := G.f_eq (below D P) a
    rw [hc1] at this
    simpa using this
  have hSf' : ∀ a, (G.S (below D P)).f' a = (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).bc (below D P) (G.f' a) := by
    intro a
    have := G.f'_eq (below D P) a
    rw [hc1] at this
    simpa using this
  have hiso : n⁻¹ * t₀.lin * m ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hn.1) t₀.rep.2.2.1) hm.1
  have hfr : ∀ b, frame (mapLF (n⁻¹ * t₀.lin * m) (lf D (X.Fu u'))) b = (n⁻¹ * t₀.lin * m) (frame (lf D (X.Fu u')) b) := by
    intro b
    unfold mapLF
    rw [dite_eq_left hiso]
    simp only [frame, Formalism.MainNotions.S.FlagG.fvec, mapFlag]
    exact (congrFun (Fin.comp_snoc (⇑(n⁻¹ * t₀.lin * m)) _ _) b).symm
  have hyin : ∀ a, frame (lf D (X.Fu u)) a ∈ t₀.lam := fun a => GlobalTheory.T.fixedFrame_mem_rowLattices_of_word D X Y u t₀.lam t₀.mem a
  have hxin : ∀ b, frame (mapLF (n⁻¹ * t₀.lin * m) (lf D (X.Fu u'))) b ∈ t₀.lam := by
    intro b
    rw [hfr b, ← hgm]
    exact Submodule.mem_map_of_mem (GlobalTheory.T.fixedFrame_mem_rowLattices_of_word D X Y u' t₀.lam' t₀.mem' b)
  have hy : ∀ b, c.e ((ρ * n) (frame (lf D (X.Fu u)) b)) = ∑ a, B a b • G.f a := by
    intro b

    rw [LinearEquiv.mul_apply, (hBB b).1, map_sum]
    simp only [map_smul, c.f_eq]
  have hx : ∀ b, c.e ((ρ * n) (frame (mapLF (n⁻¹ * t₀.lin * m) (lf D (X.Fu u'))) b)) = ∑ a, B' a b • G.f' a := by
    intro b

    rw [LinearEquiv.mul_apply, (hBB b).2, map_sum]
    simp only [map_smul, c.f'_eq]
  have hmemc : ∀ v ∈ t₀.lam, c.e ((ρ * n) v) ∈ c.lat (ρ * n) t₀.lam := fun v hv =>
    Submodule.mem_map.2 ⟨v, hv, rfl⟩
  haveI := ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc (below D P)).lf
  haveI := ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc (below D P)).char0
  obtain ⟨ξp, hξO, hξ1, hξ2, hξT⟩ := GlobalTheory.T.term_frames_congr_mod_theta_unitriangular _ D.R.rS D.R.k (G.S (below D P)) (d (below D P))
    ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).lat (below D P) (c.lat (ρ * n) t₀.lam)) (hloc (below D P))
    (fun b => (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).bc (below D P) (c.e ((ρ * n) (frame (lf D (X.Fu u)) b))))
    (fun b => (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).bc (below D P) (c.e ((ρ * n) (frame (mapLF (n⁻¹ * t₀.lin * m) (lf D (X.Fu u'))) b))))
    (fun a b => ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc (below D P)).ιE (B a b)) (fun a b => ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc (below D P)).ιE (B' a b))
    (fun a b h => by simp [hB1 a b h]) (fun a => by simp [hB2 a])
    (fun a b h => by simp [hB1' a b h]) (fun a => by simp [hB2' a])
    (fun b => by simp only [hy, bc_sum, hSf])
    (fun b => by simp only [hx, bc_sum, hSf'])
    (fun a => Submodule.subset_span ⟨_, hmemc _ (hyin a), rfl⟩)
    (fun b => Submodule.subset_span ⟨_, hmemc _ (hxin b), rfl⟩)
  have hfg : (c.lat (ρ * n) t₀.lam).FG := hlat.fg
  have hpos : 0 < _root_.Formalism.MainNotions.S.Lat.gS D := by
    unfold _root_.Formalism.MainNotions.S.Lat.gS
    exact Nat.mul_pos (D.host.g_prime 0).pos (D.host.g_prime 1).pos
  obtain ⟨ξ, hu1, hu2, hPP⟩ := GlobalTheory.T.exists_global_unitriangular_of_local_congruence (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)) _ D.R.rS (c.lat (ρ * n) t₀.lam) hfg
    (_root_.Formalism.MainNotions.S.Lat.gS D) hpos (below D P)
    (fun b => c.e ((ρ * n) (frame (lf D (X.Fu u)) b)))
    (fun b => c.e ((ρ * n) (frame (mapLF (n⁻¹ * t₀.lin * m) (lf D (X.Fu u'))) b))) ξp hξO hξ1 hξ2
    (fun a => Submodule.subset_span ⟨_, hmemc _ (hyin a), rfl⟩)
    (fun b => (GlobalTheory.T.theta_smul_completedLattice_iff_typePrimeMul D X Y F00 F'0 FP G c P hP (c.lat (ρ * n) t₀.lam) _).1 (hξT b))
  refine ⟨ξ, hu1, hu2, fun b => ?_⟩
  have h := hPP P rfl b
  set v := frame (mapLF (n⁻¹ * t₀.lin * m) (lf D (X.Fu u'))) b - frameAct (frame (lf D (X.Fu u))) ξ b with hv
  have hφ : c.e ((ρ * n) (frame (mapLF (n⁻¹ * t₀.lin * m) (lf D (X.Fu u'))) b)) -
      ∑ a, ((ξ a b : 𝓞 D.host.E) : D.host.E) • c.e ((ρ * n) (frame (lf D (X.Fu u)) a)) = c.e ((ρ * n) v) := by
    rw [hv, map_sub, map_sub]

    simp only [frameAct, map_sum, map_smul]
  rw [hφ] at h
  have hmap : Ideal.span {((_root_.Formalism.MainNotions.S.Lat.gS D : ℕ) : 𝓞 D.host.E)} • c.lat (ρ * n) t₀.lam =
      (Ideal.span {((_root_.Formalism.MainNotions.S.Lat.gS D : ℕ) : 𝓞 D.host.E)} • t₀.lam).map
        ((((ρ * n).trans c.e : (VS D).V ≃ₗ[D.host.E] G.V) : (VS D).V →ₗ[D.host.E] G.V).restrictScalars (𝓞 D.host.E)) := by
    unfold GCoord.lat
    rw [Submodule.map_smul'']
  rw [hmap] at h
  obtain ⟨s, hs, hsv⟩ := h
  refine ⟨s, hs, ?_⟩
  obtain ⟨z, hz, hzv⟩ := Submodule.mem_map.1 hsv
  have hinj : Function.Injective ((((ρ * n).trans c.e : (VS D).V ≃ₗ[D.host.E] G.V) : (VS D).V →ₗ[D.host.E] G.V).restrictScalars (𝓞 D.host.E)) :=
    ((ρ * n).trans c.e).injective
  have : z = s • v := by
    apply hinj
    rw [hzv, LinearMap.map_smul]
    rfl
  rw [← this]
  exact hz

end GlobalTheory.HL.LocCong
end
end

section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.mem_rationalUnipotent_of_local_extension : ∀ (D : D7) (Z : LocDat D) (p : PlF D) {T : D.host.E} (F : LFlag (D.sp.Y 0) D.R.rS T) (γ : (VS D).V ≃ₗ[D.host.E] (VS D).V) (g : Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p), GlobalTheory.LocOver.Ext p γ g → g ∈ NU (locH Z p) (scaled Z p (frame F)) → γ ∈ NRat F := by
  first | exact @GlobalTheory.LocReflect.mem_nrat_of_ext | exact GlobalTheory.LocReflect.mem_nrat_of_ext | (intros; apply GlobalTheory.LocReflect.mem_nrat_of_ext <;> assumption)
end

section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.moves_to_determines_unipotent_factorisation : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word) (F00 : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F'0 : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (t₀ : TauC Y u u') (ρ : (VS D).V ≃ₗ[D.host.E] (VS D).V) (U U' : Formalism.L2.SG.PairVal.MatR D), MovesTo F00 F'0 (lf D (X.Fu u)) t₀.frame ρ U U' → ∀ (t : TauC Y u u') n m, n ∈ NRat (lf D (X.Fu u)) ∧ m ∈ NRat (lf D (X.Fu u')) ∧ t.lin = n⁻¹ * t₀.lin * m → ∃ A A' : Formalism.L2.SG.PairVal.MatR D, IsUpUni A ∧ IsUpUni A' ∧ (∀ b, n (frame (lf D (X.Fu u)) b) = ∑ a, A a b • frame (lf D (X.Fu u)) a) ∧ (∀ b, m (frame (lf D (X.Fu u')) b) = ∑ a, A' a b • frame (lf D (X.Fu u')) a) ∧ MovesTo F00 F'0 (lf D (X.Fu u)) t.frame (ρ * n) (U * A) (U' * A') := by
  first | exact @GlobalTheory.FrameStep.step | exact GlobalTheory.FrameStep.step | (intros; apply GlobalTheory.FrameStep.step <;> assumption)
end

section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.FourierDecayAlt Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.SnFam
open scoped Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ScalSymm

open Formalism.L2.SG.NGCut

theorem scal_symm : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ∀ t t' : TauC Y u u', t.G ≠ 0 → t'.G ≠ 0 → (Y.tO u u').s0 t t' = 1 → (Y.tO u u').scal t t' → (Y.tO u u').s0 t' t = 1 ∧ (Y.tO u u').scal t' t := by
  intro D X Y u u' t t' hG hG' hs hsc
  have hdim := Formalism.L2.SG.Corank.finrank_VS D
  have hGv : ∀ t : TauC Y u u', t.G ≠ 0 → Gval (lf D (X.Fu u)) t.frame ≠ 0 := fun t h =>
    (Formalism.L2.SG.Pf.SatGram.gterm_G Y t) ▸ h
  have hlat : ∀ t : TauC Y u u', Submodule.IsFullLattice D.host.E t.lam := fun t =>
    ((Y.rowsOK u).1 t.lam t.mem).1.1
  have hLF : ∀ t : TauC Y u u', IsLift t.lam (lf D (X.Fu u)) := fun t =>
    ((Y.rowsOK u).1 t.lam t.mem).2.1.2.2.1
  have hLt : ∀ t : TauC Y u u', IsLift t.lam t.frame := fun t => t.rep.2.2.2.2.1
  obtain ⟨⟨hlam, hlam'⟩, -, hIS⟩ := (show Formalism.L2.SG.TermOp.scalT t t' from hsc)
  have h1' : Formalism.L2.SG.TermOp.s0T t t' = 1 := hs
  unfold Formalism.L2.SG.TermOp.s0T at h1'
  rw [if_pos ⟨hlam, hlam'⟩] at h1'
  have hth := (CorankRelation.s0_eq_one_iff_Th_eq_Hp D.R.k hdim t.lam (hlat t) _ t.frame t'.frame _ (hLF t) (hLt t)
    (hGv t hG)).1 h1'
  have hL' : IsLift t.lam t'.frame := by rw [hlam]; exact hLt t'
  have hsym := CorankRelation.Th_symm D.R.k hdim t.lam (hlat t) _ t.frame t'.frame (t'.lin * t.lin⁻¹) (hLF t) (hLt t) hL'
    (hGv t hG) (hGv t' hG') (CorankRelation.frame_mem_iff t t') hth
  have hinv : (t'.lin * t.lin⁻¹)⁻¹ = t.lin * t'.lin⁻¹ := by group
  rw [hinv] at hsym
  have hs' : s0 t.lam (lf D (X.Fu u)) t'.frame t.frame (t.lin * t'.lin⁻¹) D.R.k = 1 :=
    (CorankRelation.s0_eq_one_iff_Th_eq_Hp D.R.k hdim t.lam (hlat t) _ t'.frame t.frame _ (hLF t) hL' (hGv t' hG')).2 hsym
  have hback : ∀ y : (VS D).V, (t'.lin * t.lin⁻¹) ((t.lin * t'.lin⁻¹) y) = y := fun y => by
    show t'.lin (t.lin.symm (t.lin (t'.lin.symm y))) = y
    simp
  refine ⟨?_, ?_⟩
  · show Formalism.L2.SG.TermOp.s0T t' t = 1
    unfold Formalism.L2.SG.TermOp.s0T
    rw [if_pos ⟨hlam.symm, hlam'.symm⟩, ← hlam]
    exact hs'
  · show Formalism.L2.SG.TermOp.scalT t' t
    refine ⟨⟨hlam.symm, hlam'.symm⟩, ?_, ?_⟩
    · rw [← hlam]; exact hs'
    · rw [← hlam]
      intro y2 hy2 y1 hy1 y2'' hy2'' y1' hy1' hd hd' al al'
      have hd1 : y1 - y2 ∈ Xsp (lf D (X.Fu u)) := by
        have := (Xsp (lf D (X.Fu u))).neg_mem hd
        simpa using this
      have hd2 : y2'' - (t'.lin * t.lin⁻¹) y1' ∈ Xsp t'.frame := by
        have h := (CorankRelation.frame_mem_iff t t' _).1 hd'
        rw [map_sub, hback] at h
        have := (Xsp t'.frame).neg_mem h
        simpa using this
      exact (hIS y1 hy1 y2 hy2 y1' hy1' y2'' hy2'' hd1 hd2 al al').symm

end GlobalTheory.ScalSymm
end
end

section

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf Formalism.L2.SG.LoopTieOf
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Matrix

theorem _root_.GlobalTheory.T.rationalLink_conjugate_mem_integralRealPoints : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (W : WittDat X) (u u' : D.what₂.Word) (s : TT Y u u') (n : (VS D).V ≃ₗ[D.host.E] (VS D).V), n ∈ NLam (Formalism.HermitianLatticesTheory.gmap (W.δ u) s.lam) (lf D (FlagOfWord W u)) ∩ NLam (Formalism.HermitianLatticesTheory.gmap (W.δ u) s.lam) (Formalism.L2.SG.Saturated.mapL (W.δ u) (W.isom u) s.frame) → ∃ x : X.B.I.GA, Formalism.L2.SG.TermOp.RatLink X x ((W.δ u)⁻¹ * n * W.δ u) ∧ x.1 ∈ Formalism.L2.SG.TermOp.ROinf s := by
  first | exact @GlobalTheory.CoverAct.ratLink_mem_ROinf | exact GlobalTheory.CoverAct.ratLink_mem_ROinf | (intros; apply GlobalTheory.CoverAct.ratLink_mem_ROinf <;> assumption)
end

section

open NumberField Module Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt GlobalTheory.LoopC
open scoped ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.card_middleLattices_over_genus_lattice : ∀ (D : D7) (u : D.what₂.Word), (Tu D u).Prime → 3 ≤ Tu D u → SplitsCompletely (E := D.host.E) (Tu D u) → ∀ F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E), F0.e = D.sp.hypE → F0.z = D.zmOf u → ∀ Λ : LatV D, IsRowLat D F0 Λ → ∀ M ∈ Formalism.HermitianLatticesTheory.genus (D.sp.X 0).hT (L0X D Λ (lf D F0)), {𝓛 : Submodule (𝓞 D.host.E) ((D.sp.X 0).V × D.host.E) | (∃ Λ', IsRowLat D F0 Λ' ∧ (Lsub Λ' (lf D F0)).comap (((D.sp.iXY 0).coprod (LinearMap.toSpanSingleton D.host.E (VS D).V F0.z)).restrictScalars (𝓞 D.host.E)) = 𝓛) ∧ 𝓛.comap ((LinearMap.inl D.host.E (D.sp.X 0).V D.host.E).restrictScalars (𝓞 D.host.E)) = M}.ncard = (Tu D u - 1) ^ D.R.f := by
  first | exact @GlobalTheory.LoopC.GluingNum.gluingNum | exact GlobalTheory.LoopC.GluingNum.gluingNum | (intros; apply GlobalTheory.LoopC.GluingNum.gluingNum <;> assumption)
end

section

open NumberField Module Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt GlobalTheory.LoopC
open scoped ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.row_lattices_same_middle_conjugate_unipotent : ∀ (D : D7) (u : D.what₂.Word), (Tu D u).Prime → 3 ≤ Tu D u → SplitsCompletely (E := D.host.E) (Tu D u) → ∀ F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E), F0.e = D.sp.hypE → F0.z = D.zmOf u → ∀ Λ₁ Λ₂ : LatV D, IsRowLat D F0 Λ₁ → IsRowLat D F0 Λ₂ → Lsub Λ₁ (lf D F0) = Lsub Λ₂ (lf D F0) → ∃ n ∈ stabF D F0, (∀ x ∈ orth (hS D) F0.X, n x - x ∈ F0.X) ∧ Formalism.HermitianLatticesTheory.gmap n Λ₁ = Λ₂ := by
  first | exact @GlobalTheory.LoopC.rowsLift | exact GlobalTheory.LoopC.rowsLift | (intros; apply GlobalTheory.LoopC.rowsLift <;> assumption)
end

section

open GlobalTheory.FlagMeas GlobalTheory.GaussMean

namespace GlobalTheory.GaussMean

theorem volumeStep_of_siegelWeil :
    HeckeCharacterZeroLocus.SiegelWeilU.SiegelWeilUnitaryConvergent → VolumeStep := fun h =>
  GlobalTheory.GaussMean.Step.volumeStep_of_siegelMean
    (GlobalTheory.GaussMean.Limit.siegelMean_of_cc
      (GlobalTheory.OneVectorMean.siegelMeanCc_of_oneVectorCc
        (GlobalTheory.GaussMean.oneVectorCc_of_siegelWeil h)))

end GlobalTheory.GaussMean
end
