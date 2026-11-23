module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle695
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle705
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RepresentationAtEveryPlace
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle703
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.Bundle002
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SubsetPlaceVectorsAndSteps
public import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle037
public import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RightTranslationLiftEqLevelMoveUnitConst
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle330
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle282
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle090
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FrameUniformEmbeddingSecond
import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleLayerExistsGenerators
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle318
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle469
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle574

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal GlobalTheory.FinPl
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField


theorem _root_.GlobalTheory.T.lattice_off_S0_last_level_iff : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (v : GlobalTheory.FinPl.Pl D), v ∉ G.pl.S0 → ∀ y : Fin (G.V (.grid D.R.m 0)).rank → AE D, (∀ i, y i ∈ idAt D (· = v)) → (y ∈ GlobalTheory.FinPl.latV _ (G.Λ (.grid D.R.m 0)) (· = v) ↔ y ∈ GlobalTheory.FinPl.latV _ (GlobalTheory.RowShape.rowN G 0) (· = v)) := by
  first | exact @GlobalTheory.RowShape.latV_grid_iff_rowN_zero | exact GlobalTheory.RowShape.latV_grid_iff_rowN_zero | (intros; apply GlobalTheory.RowShape.latV_grid_iff_rowN_zero <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
open GlobalTheory.RootEx GlobalTheory.RowRep
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.RowRepBes
open GlobalTheory.LocGrp GlobalTheory.LocMod

theorem mem_bes {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k)
    {A B : HSp D} {σ : ℕ} (d : HermitianOrthogonalExtensionData A B (2 * σ + 1) (-1)) (l : Fin σ → D.host.E) (hl : ∀ a, l a ≠ 0)
    {b b' : Matrix (Fin A.rank) (Fin A.rank) k} (hb : b * b' = 1) (hb' : b' * b = 1) {u : Fin (2 * σ + 1) → k}
    {Γ : Matrix (Fin A.rank ⊕ Fin (2 * σ + 1)) (Fin B.rank) k} (h1 : Γ * sumCols d p.π b u = 1) (h2 : sumCols d p.π b u * Γ = 1)
    {g : GA D B} (hg : SuppAt p.e B g) {x : GL (Fin A.rank ⊕ Fin (2 * σ + 1)) k}
    (e : Eq (α := Matrix (Fin A.rank ⊕ Fin (2 * σ + 1)) (Fin A.rank ⊕ Fin (2 * σ + 1)) k)
      x.val (Γ * ((mt B g).map p.π * sumCols d p.π b u))) (hx : x ∈ symR k (Fin A.rank) (2 * σ + 1)) :
    g ∈ besGrp (diagDec (besDec d rfl) l hl) (GlobalTheory.OrthSumExists.orthDecHsum D _ _) := by
  have hσ : σ ≤ 2 * σ + 1 := by omega
  have hσ' : σ < 2 * σ + 1 := by omega
  let E : Fin A.rank ⊕ Fin 1 ≃ Fin (GlobalTheory.Doubling.hsum A (GlobalTheory.SeeSaw.Model.nLine D)).rank := finSumFinEquiv
  let φ : D.host.E →+* k := p.π.comp (incA D)
  set dd := diagDec (besDec d rfl) l hl with hdd
  set o := GlobalTheory.OrthSumExists.orthDecHsum D A (GlobalTheory.SeeSaw.Model.nLine D) with ho
  let F : Frame k B.rank (Fin A.rank ⊕ Fin (2 * σ + 1)) := { β := sumCols d p.π b u, γ := Γ, βγ := h2, γβ := h1 }
  let FA : Frame k A.rank (Fin A.rank) := { β := b, γ := b', βγ := hb, γβ := hb' }
  let F₀ : Frame k (GlobalTheory.Doubling.hsum A (GlobalTheory.SeeSaw.Model.nLine D)).rank (Fin A.rank ⊕ Fin 1) :=
    { β := (fromBlocks b 0 0 (1 : Matrix (Fin 1) (Fin 1) k)).submatrix E.symm id
      γ := (fromBlocks b' 0 0 (1 : Matrix (Fin 1) (Fin 1) k)).submatrix id E.symm
      βγ := by
        refine (submatrix_mul_equiv _ _ _ (Equiv.refl _) _).trans ?_
        rw [fromBlocks_multiply]
        simp [hb]
      γβ := by
        refine (submatrix_mul_equiv _ _ _ E.symm _).trans ?_
        rw [fromBlocks_multiply]
        simp [hb'] }
  have hloc : p.IsLoc F g x := by
    refine ⟨hg, ?_⟩
    change _ = sumCols d p.π b u * x.val * Γ
    rw [e, ← Matrix.mul_assoc, h2, Matrix.one_mul, Matrix.mul_assoc, h2, Matrix.mul_one]
  have vX : ∀ r (i : Fin σ), φ (d.a r (Fin.castLE hσ i)) = φ (l i)⁻¹ * (dd.jX.map p.π) r i := fun r i => by
    change _ = _ * φ (((besDec d rfl).e * diagonal l) r i)
    rw [mul_diagonal, ← map_mul, mul_left_comm, inv_mul_cancel₀ (hl i), mul_one]; rfl
  have vY : ∀ r (i : Fin σ), φ (d.a r (Fin.castLE hσ i).rev) = φ (star (l i)) * (dd.jY.map p.π) r i :=
    fun r i => by
      change _ = _ * φ (((besDec d rfl).e' * diagonal fun a => (star (l a))⁻¹) r i)
      rw [mul_diagonal, ← map_mul, mul_left_comm, mul_inv_cancel₀ (star_ne_zero.2 (hl i)), mul_one]; rfl
  have core : ∀ {Z : Type} (X : Matrix (Fin A.rank ⊕ Fin 1) Z k), dd.j0.map p.π *
      X.submatrix E.symm id = fromCols ((frameMat B A d.ι).map φ) ((midCol d rfl).map φ) * X := fun X => by
    have e : dd.j0.map p.π = (fromCols ((frameMat B A d.ι).map φ) ((midCol d rfl).map φ)).submatrix id E.symm := by
      rw [← fromCols_map]; rfl
    exact (congrArg (· * X.submatrix E.symm id) e).trans (submatrix_mul_equiv _ _ _ E.symm _)
  have jA : dd.j0.map p.π * o.jA.map p.π = (frameMat B A d.ι).map φ := by
    have e : o.jA.map p.π = (fromRows (1 : Matrix (Fin A.rank) (Fin A.rank) k) (0 : Matrix (Fin 1) (Fin A.rank) k)).submatrix E.symm id := by
      rw [← Matrix.map_one φ (map_zero _) (map_one _), ← Matrix.map_zero φ (map_zero _), ← fromRows_map]; rfl
    rw [e, core, fromCols_mul_fromRows, Matrix.mul_one, Matrix.mul_zero, add_zero]
  have jB : dd.j0.map p.π * o.jB.map p.π = (midCol d rfl).map φ := by
    have e : o.jB.map p.π = (fromRows (0 : Matrix (Fin A.rank) (Fin 1) k) (1 : Matrix (Fin 1) (Fin 1) k)).submatrix E.symm id := by
      rw [← Matrix.map_one φ (map_zero _) (map_one _), ← Matrix.map_zero φ (map_zero _), ← fromRows_map]; rfl
    refine (congrArg (dd.j0.map p.π * ·) e).trans ((core _).trans ?_)
    rw [fromCols_mul_fromRows, Matrix.mul_one, Matrix.mul_zero, zero_add]
  have fX : ∀ (i : Fin σ) r, F.β r (Sum.inr (Fin.castLE hσ i)) = u (Fin.castLE hσ i) * φ (l i)⁻¹ * (dd.jX.map p.π) r i :=
    fun i r => (mul_diagonal u _ _ _).trans ((mul_comm _ _).trans ((congrArg (u _ * ·) (vX r i)).trans (mul_assoc _ _ _).symm))
  have fY : ∀ (i : Fin σ) r, F.β r (Sum.inr (Fin.castLE hσ i).rev) =
      u (Fin.castLE hσ i).rev * φ (star (l i)) * (dd.jY.map p.π) r i :=
    fun i r => (mul_diagonal u _ _ _).trans ((mul_comm _ _).trans ((congrArg (u _ * ·) (vY r i)).trans (mul_assoc _ _ _).symm))
  have fZ : ∀ r, F.β r (Sum.inr ⟨σ, hσ'⟩) = u ⟨σ, hσ'⟩ * (dd.j0.map p.π * o.jB.map p.π) r (0 : Fin 1) := fun r =>
    (mul_diagonal u _ _ _).trans ((mul_comm _ _).trans (congrArg (u _ * ·) (congrFun (congrFun jB r) (0 : Fin 1)).symm))
  have ec := core (fromBlocks b 0 0 (1 : Matrix (Fin 1) (Fin 1) k))
  rw [fromCols_mul_fromBlocks, Matrix.mul_zero, Matrix.mul_zero, add_zero, zero_add, Matrix.mul_one] at ec
  obtain ⟨Φ, hΦ⟩ := exists_hom p F
  have hN : N k (Fin A.rank) (2 * σ + 1) (σ + 1) ≤ (besGrp dd o).comap Φ := by
    refine (Subgroup.closure_le _).2 fun y hy => Subgroup.mem_sup_left (flag_of_strict p dd F₀ F
      (Sum.elim (Sum.map id fun _ => ⟨σ, hσ'⟩)
        (Sum.elim (fun i : Fin σ => Sum.inr (Fin.castLE hσ i)) fun i : Fin σ => Sum.inr (Fin.castLE hσ i).rev)) ?_
      (Sum.elim (Sum.elim (fun _ => 1) fun _ => u ⟨σ, hσ'⟩)
        (Sum.elim (fun i => u (Fin.castLE hσ i) * φ (l i)⁻¹) fun i => u (Fin.castLE hσ i).rev * φ (star (l i)))) ?_
      (GlobalTheory.RootEx.lev (σ + 1)) ?_ (hΦ y) fun r s hrs => by rw [Matrix.sub_apply, hy r s hrs, sub_self])
    · rintro (a | j)
      · exact ⟨Sum.inl (Sum.inl a), rfl⟩
      · rcases lt_trichotomy j.val σ with h | h | h
        · exact ⟨Sum.inr (Sum.inl ⟨j.val, h⟩), rfl⟩
        · exact ⟨Sum.inl (Sum.inr 0), congrArg Sum.inr (Fin.ext h.symm)⟩
        · exact ⟨Sum.inr (Sum.inr ⟨2 * σ - j.val, by omega⟩), congrArg Sum.inr (Fin.ext (by
            simp only [Fin.val_rev, Fin.val_castLE]; omega))⟩
    · rintro r ((a | a) | i | i)
      · exact (congrFun (congrFun ec r) (Sum.inl a)).symm.trans (one_mul _).symm
      · exact (mul_diagonal u _ _ _).trans ((mul_comm _ _).trans (congrArg (u _ * ·) (congrFun (congrFun ec r) (Sum.inr a)).symm))
      · exact fX i r
      · exact fY i r
    · rintro ((a | a) | i | i)
      · rfl
      · rfl
      · rfl
      · have := i.2
        simp only [GlobalTheory.RootEx.lev, wlev, Sum.elim_inr, Fin.val_rev, Fin.val_castLE]
        omega
  have hle : symR k (Fin A.rank) (2 * σ + 1) ≤ (besGrp dd o).comap Φ := by
    rw [symR, symN_odd]
    refine sup_le ?_ hN
    rintro _ ⟨g₀, rfl⟩
    obtain ⟨h, hh⟩ := Witness.exists_isLoc p FA g₀
    have eA : mt B (dd.emb0 (o.emb (h, 1))) ⬝ (dd.j0 ⬝ o.jA) = dd.j0 ⬝ o.jA ⬝ mt A h := by
      rw [cancel₂ (dd.wittDecomp_anisotropicEmbedding_inclAnisotropic _), Matrix.mul_assoc, o.emb_jA, Matrix.mul_assoc]
    have eB : mt B (dd.emb0 (o.emb (h, 1))) ⬝ (dd.j0 ⬝ o.jB) = dd.j0 ⬝ o.jB := by
      rw [cancel₂ (dd.wittDecomp_anisotropicEmbedding_inclAnisotropic _), Matrix.mul_assoc, o.emb_jB, GlobalTheory.MixModel.mt_one, Matrix.mul_one]
    have eZ := map_fix p eB
    rw [Matrix.map_mul] at eZ
    have hm : p.IsLoc F (dd.emb0 (o.emb (h, 1))) (embX (2 * σ + 1) g₀) := by
      refine ⟨suppAt_wittLeviEmbedding dd (suppAt_emb o hh.1), eq_embX F _ g₀ ((dd.j0 ⬝ o.jA).map p.π * FA.β) (fun r a => ?_)
        (intertwine p eA hh) fun j => ?_⟩
      · change ((frameMat B A d.ι).map φ * b) r a = _
        rw [Matrix.map_mul, jA]
      · rcases lt_trichotomy j.val σ with hj | hj | hj
        · exact fix_col (map_fix p (dd.wittDecomp_anisotropicEmbedding_inclX _)) _ ⟨j.val, hj⟩ (fX ⟨j.val, hj⟩)
        · obtain rfl : j = ⟨σ, hσ'⟩ := Fin.ext hj
          exact fix_col eZ _ (0 : Fin 1) fZ
        · obtain ⟨q, rfl⟩ : ∃ q : Fin σ, j = (Fin.castLE hσ q).rev :=
            ⟨⟨2 * σ - j.1, by omega⟩, Fin.ext (by simp only [Fin.val_rev, Fin.val_castLE]; omega)⟩
          exact fix_col (map_fix p (dd.wittDecomp_anisotropicEmbedding_inclY _)) _ q (fY q)
    change Φ _ ∈ besGrp _ _
    rw [isLoc_unique p (hΦ _) hm]
    exact Subgroup.mem_sup_right ⟨h, rfl⟩
  rw [isLoc_unique p hloc (hΦ x)]
  exact hle hx

end GlobalTheory.RowRepBes

namespace GlobalTheory.RowRepBes
open GlobalTheory.LocMod

theorem mem_besGrp_of_symR {D : D7} {A B : HSp D} {c σ : ℕ} (d : HermitianOrthogonalExtensionData A B c (-1)) (h : c = 2 * σ + 1)
    (l : Fin σ → D.host.E) (hl : ∀ a, l a ≠ 0) (w : Pl D.host.E) (β : GL (Fin A.rank) (Lev.EAf D))
    (β' : GL (Fin B.rank) (Lev.EAf D)) (u : Fin c → Kw w) (hF : IsSumFrame d w β β' u) {a b : ℕ} (ha : a = A.rank)
    (hb : b = B.rank) (hab : a + c = b) (p : Place D (Kw w)) (hp : piAt w = p.π) (g : GA D B) (hg : SuppAt p.e B g)
    (hx : frameGL hab (inBasis hb β' w (Lev.finE B g)) ∈ symR (Kw w) (Fin a) c) :
    g ∈ besGrp (diagDec (besDec d h) l hl) (GlobalTheory.OrthSumExists.orthDecHsum D _ _) := by
  subst h ha hb
  obtain ⟨Γ, h1, h2, e⟩ := frame_val d w hF
  rw [hp] at h1 h2 e
  exact mem_bes p d l hl (GlobalTheory.StdFrames.loc w β).mul_inv (GlobalTheory.StdFrames.loc w β).inv_mul h1 h2 hg (e g) hx

theorem mem_besGrp_of_locAt : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) {t : T}, t ∈ U → ∀ {w : Pl D.host.E}, w ∈ locPl G t → ∀ (ew : AE D), Formalism.L2.NTheta.IsIdemAt ew w → ∀ {j σ : ℕ} (hj : j ≤ D.R.m) (hj' : j < D.R.m) (h' : j + 2 * σ + 2 = D.R.m) (h : GA D (G.V (.grid D.R.m j))), SuppAt ew _ h → GlobalTheory.RowRep.locAt S.B t w j hj h ∈ rowR (G := locGrid G t w) one_le_sLen (j := j) hj' → h ∈ besGrp (besDecAt G j σ h') (GlobalTheory.OrthSumExists.orthDecHsum D _ _) := by
  intro D T L sc G W U S t ht w hw ew hew j σ hj hj' h' h hs hx
  have he : IsIdemSum ew {w} := ⟨⟨fun _ => ew, fun PP hPP => by rw [Finset.mem_singleton.1 hPP]; exact hew,
    (Finset.sum_singleton (fun _ => ew) w).symm⟩, hew.1.2.1⟩
  obtain ⟨p, hp, rfl⟩ := GlobalTheory.PlcAtW.exists_plc D w ew he
  exact mem_besGrp_of_symR (G.rowDec j hj') (by omega) _ _ w _ _ _ (S.row t ht w hw j hj') (topRank_eq G t w hj)
    (rank_vertex G t w (X := (D.R.m, j)) ⟨le_rfl, hj⟩) _ p (RingHom.ext fun x => (hp.2.1 x).symm) h hs hx

end GlobalTheory.RowRepBes

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

theorem _root_.GlobalTheory.T.subset_place_vectors_and_steps : Big fun {D} _ _ _ _ {T} _ _ _ _ _ _ ch => ∀ (t : T) (e : AE D), IsIdemSum e (locPl ch.G t) → ∀ (φ : (∀ w : locPl ch.G t, ∀ b : GlobalTheory.SplitFlip.Edge, Matrix (Fin ((locGrid ch.G t w.1).rank b.tgt)) (Fin ((locGrid ch.G t w.1).rank b.src)) (Kw w.1) → ℂ)), (∀ w : locPl ch.G t, ∀ b ∈ GlobalTheory.SplitFlip.oppositePath D.R.m, GlobalTheory.SplitFlip.IsNatDatum (unifAt w.1) (depthAt ch.G w.1) (φ w b)) → ∀ (fd : SchDown ch.G t), (∀ j : Fin D.R.m, IsLocVec ch.W (.mu t D.R.m j) e (ch.rm.vT D.R.m j) (fun y => if IsHalf e y then ∏ w : locPl ch.G t, φ w (.theta D.R.m j) (ch.S.B.coord t w.1 (X := (D.R.m, j + 1)) (Y := (D.R.m, j)) ⟨le_rfl, j.2⟩ ⟨le_rfl, j.2.le⟩ (y.map fun a => cpt w.1 (toEAf D a))) else 0) (fd j)) → ∀ (eL : locPl ch.G t → AE D), (∀ w, IsIdemSum (eL w) {w.1}) → ∃ V : Finset (locPl ch.G t) → SchDown ch.G t, V ∅ = (fun j : Fin D.R.m => ch.rm.vT D.R.m j) ∧ V Finset.univ = fd ∧ (∀ S j, IsThetaFunO ch.W.ψ _ _ (V S j)) ∧ ∀ (S : Finset (locPl ch.G t)) (w : locPl ch.G t), w ∉ S → ∀ j : Fin D.R.m, IsLocVec ch.W (.mu t D.R.m j) (eL w) (V S j) (fun y => if IsHalf (eL w) y then φ w (.theta D.R.m j) (ch.S.B.coord t w.1 (X := (D.R.m, j + 1)) (Y := (D.R.m, j)) ⟨le_rfl, j.2⟩ ⟨le_rfl, j.2.le⟩ (y.map fun a => cpt w.1 (toEAf D a))) else 0) (V (insert w S) j) := by
  first | exact @GlobalTheory.SubsetVecs.subset_vectors | exact GlobalTheory.SubsetVecs.subset_vectors | (intros; apply GlobalTheory.SubsetVecs.subset_vectors <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.L2.Pj
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
open NumberField

namespace GlobalTheory.HeckeLatCoset

theorem selfDual_eq : ∀ (D : D7) (V : HSp D) (P : Formalism.L2.DIV.Pl D.host.E) (X Y : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)),
    Formalism.L2.Col.conjPrime₂ P ≠ P → (∀ v : Fin (V).rank → D.host.E, (∀ y ∈ X, ∃ n : ℤ, Algebra.trace ℚ D.host.E (-(-D.host.xi0) * ReciprocityTheory.ChartRestriction.G.FD.herm (-(V).gram.transpose) v y) = n) ↔ v ∈ X) → (∀ v : Fin (V).rank → D.host.E, (∀ y ∈ Y, ∃ n : ℤ, Algebra.trace ℚ D.host.E (-(-D.host.xi0) * ReciprocityTheory.ChartRestriction.G.FD.herm (-(V).gram.transpose) v y) = n) ↔ v ∈ Y) →
    (Formalism.L2.Col.conjPrime₂ P).asIdeal • X ≤ Y → (Formalism.L2.Col.conjPrime₂ P).asIdeal • Y ≤ X → X = Y := by
  intro D V P X Y hP hX hY hXY hYX
  have hcc : ∀ s : 𝓞 D.host.E,
      ReciprocityTheory.ChartRestriction.G.FD.cc ((Formalism.L2.Col.cO D.host.E s : 𝓞 D.host.E) : D.host.E) = (s : D.host.E) := by
    intro s
    show IsCMField.complexConj D.host.E (star (s : D.host.E)) = (s : D.host.E)
    exact star_star (s : D.host.E)
  have hcO : ∀ s : 𝓞 D.host.E, Formalism.L2.Col.cO D.host.E (Formalism.L2.Col.cO D.host.E s) = s := by
    intro s
    apply RingOfIntegers.ext
    show star (star (s : D.host.E)) = (s : D.host.E)
    exact star_star _
  have key : ∀ (s : 𝓞 D.host.E) (v y : Fin V.rank → D.host.E),
      ReciprocityTheory.ChartRestriction.G.FD.herm (-(V).gram.transpose) (s • v) y =
        ReciprocityTheory.ChartRestriction.G.FD.herm (-(V).gram.transpose) v (Formalism.L2.Col.cO D.host.E s • y) := by
    intro s v y
    unfold ReciprocityTheory.ChartRestriction.G.FD.herm
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    have e1 : (s • v) a = (s : D.host.E) * v a := rfl
    have e2 : (Formalism.L2.Col.cO D.host.E s • y) b = ((Formalism.L2.Col.cO D.host.E s : 𝓞 D.host.E) : D.host.E) * y b := rfl
    have e3 : ReciprocityTheory.ChartRestriction.G.FD.cc (((Formalism.L2.Col.cO D.host.E s : 𝓞 D.host.E) : D.host.E) * y b) =
        (s : D.host.E) * ReciprocityTheory.ChartRestriction.G.FD.cc (y b) := by
      rw [← hcc s]
      exact map_mul (IsCMField.complexConj D.host.E) _ _
    rw [e1, e2, e3]
    ring
  have hne : P.asIdeal ≠ (Formalism.L2.Col.conjPrime₂ P).asIdeal := fun h =>
    hP (IsDedekindDomain.HeightOneSpectrum.ext h.symm)
  have hcop : P.asIdeal ⊔ (Formalism.L2.Col.conjPrime₂ P).asIdeal = ⊤ :=
    Ideal.IsMaximal.coprime_of_ne P.isMaximal (Formalism.L2.Col.conjPrime₂ P).isMaximal hne
  obtain ⟨s, hs, t, ht, hst⟩ := Submodule.mem_sup.1 (hcop ▸ Submodule.mem_top : (1 : 𝓞 D.host.E) ∈ P.asIdeal ⊔ (Formalism.L2.Col.conjPrime₂ P).asIdeal)
  have hsc : Formalism.L2.Col.cO D.host.E s ∈ (Formalism.L2.Col.conjPrime₂ P).asIdeal := by
    rw [Formalism.L2.Col.mem_conjP, hcO]
    exact hs
  have incl : ∀ X Y : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E),
      (∀ v : Fin (V).rank → D.host.E, (∀ y ∈ X, ∃ n : ℤ, Algebra.trace ℚ D.host.E (-(-D.host.xi0) * ReciprocityTheory.ChartRestriction.G.FD.herm (-(V).gram.transpose) v y) = n) ↔ v ∈ X) → (∀ v : Fin (V).rank → D.host.E, (∀ y ∈ Y, ∃ n : ℤ, Algebra.trace ℚ D.host.E (-(-D.host.xi0) * ReciprocityTheory.ChartRestriction.G.FD.herm (-(V).gram.transpose) v y) = n) ↔ v ∈ Y) →
      (Formalism.L2.Col.conjPrime₂ P).asIdeal • X ≤ Y → (Formalism.L2.Col.conjPrime₂ P).asIdeal • Y ≤ X → Y ≤ X := by
    intro X Y hX hY hXY hYX l hl
    have h1 : t • l ∈ X := hYX (Submodule.smul_mem_smul ht hl)
    have h2 : s • l ∈ X := by
      rw [← hX]
      intro x hx
      have hx' : Formalism.L2.Col.cO D.host.E s • x ∈ Y := hXY (Submodule.smul_mem_smul hsc hx)
      obtain ⟨n, hn⟩ := (hY l).2 hl _ hx'
      exact ⟨n, by rw [key]; exact hn⟩
    have e : l = s • l + t • l := by rw [← add_smul, hst, one_smul]
    rw [e]
    exact X.add_mem h2 h1
  exact le_antisymm (incl Y X hY hX hYX hXY) (incl X Y hX hY hXY hYX)

theorem latG_mul_levG : ∀ (D : D7) {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks),
    R.toLevCh.Is A.μ0 → ∀ (i : Fin D.R.m) (x κ : GA D (Wc D i)),
    κ ∈ Lev.levG (Wc D i) (R.βW i) (R.datWp i R.triv) → latG (Wc D i) (x * κ) = latG (Wc D i) x := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R hL i x κ hκ
  have hκ' : Lev.IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) 1 κ :=
    ⟨hκ.1, hκ.2.1, Subgroup.mem_bot.1 hκ.2.2⟩
  have hS := GlobalTheory.DictMove.latGHat_eq (hL.βW i) hκ'
  ext v
  rw [(GlobalTheory.MarkCoset.latG_spec D _ (x * κ)).1, (GlobalTheory.MarkCoset.latG_spec D _ x).1,
    (GlobalTheory.MarkCoset.latG_spec D _ (x * κ)).2, (GlobalTheory.MarkCoset.latG_spec D _ x).2]
  constructor
  · rintro ⟨y, hy, hyz⟩
    refine ⟨(finHom (Wc D i) κ).1.mulVec y, ?_, ?_⟩
    · rw [← hS]
      exact ((GlobalTheory.MarkCoset.latG_spec D _ κ).2 _).2 ⟨y, hy, rfl⟩
    · rw [← hyz, map_mul, Units.val_mul, Matrix.mulVec_mulVec]
  · rintro ⟨y, hy, hyz⟩
    rw [← hS] at hy
    obtain ⟨y', hy', rfl⟩ := ((GlobalTheory.MarkCoset.latG_spec D _ κ).2 _).1 hy
    exact ⟨y', hy', by rw [← hyz, map_mul, Units.val_mul, Matrix.mulVec_mulVec]⟩

theorem exists_coset_of_selfDual : ∀ (D : D7) {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks),
    R.toLevCh.Is A.μ0 → R.IsFam → ∀ (i : Fin D.R.m) (P : Formalism.L2.DIV.Pl D.host.E) (k : ℕ) (α : GA D (Wc D i))
    (Rc : Finset (GA D (Wc D i))),
    Bridge.SplitOff P (R.Sb : Set (Formalism.L2.DIV.Pl D.host.E)) → IsHeckeAt (Wc D i) P k α →
    Bridge.IsDC (Lev.levG (Wc D i) (R.βW i) (R.datWp i R.triv)) α Rc →
    ∀ (g : GA D (Wc D i)) (L' : Submodule (𝓞 D.host.E) (Fin (Wc D i).rank → D.host.E)),
    P.asIdeal • latG (Wc D i) g ≤ L' → (Formalism.L2.Col.conjPrime₂ P).asIdeal • L' ≤ latG (Wc D i) g →
    (∀ v : Fin (Wc D i).rank → D.host.E, (∀ y ∈ L', ∃ n : ℤ, Algebra.trace ℚ D.host.E (-(-D.host.xi0) * ReciprocityTheory.ChartRestriction.G.FD.herm (-(Wc D i).gram.transpose) v y) = n) ↔ v ∈ L') →
    (L' ⊓ latG (Wc D i) g).toAddSubgroup.relIndex (latG (Wc D i) g).toAddSubgroup = Ideal.absNorm P.asIdeal ^ k →
    ∃ a ∈ Rc, latG (Wc D i) (g * a) = L' ∧ ∃ (e : AE D) (a₀ : GA D (Wc D i)), Formalism.L2.NTheta.IsIdemAt e P ∧
      SuppAt e (Wc D i) a₀ ∧ a⁻¹ * a₀ ∈ Lev.levG (Wc D i) (R.βW i) (R.datWp i R.triv) ∧ latG (Wc D i) (g * a₀) = L' := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R hL hF i P k α Rc hso hα hRc g L' h1 h2 hsd hidx
  obtain ⟨e, ϖ, he, hϖ1, hϖ2, hαe⟩ := hα
  have hP : Formalism.L2.Col.conjPrime₂ P ≠ P := by
    intro h
    apply hso.1
    rw [Formalism.L2.Col.conjIdeal_asIdeal, h]
  obtain ⟨a₀, ha₀, hT, hT2⟩ := GlobalTheory.T.exists_heckeElement_lattice_between_prime_mul_split D (Wc D i) P e ϖ k g (L' ⊓ latG (Wc D i) g) he hϖ1 hϖ2
    (le_inf h1 Submodule.smul_le_right) inf_le_right hidx
  obtain ⟨a, ha, hK⟩ := GlobalTheory.T.exists_coset_rep_hecke_element_principal_level D R hL hF i P k α Rc e ϖ a₀ hso ⟨e, ϖ, he, hϖ1, hϖ2, hαe⟩ hRc he hϖ1 hϖ2 ha₀
  have hTL : latG (Wc D i) (g * a₀) = L' := by
    refine selfDual_eq D (Wc D i) P _ _ hP (GlobalTheory.Member.latG_selfDual D (Wc D i) (g * a₀) _ rfl).2.2 hsd ?_ ?_
    · refine le_trans ?_ (inf_le_left : L' ⊓ latG (Wc D i) g ≤ L')
      rw [← hT]
      exact le_inf Submodule.smul_le_right hT2
    · refine le_trans ?_ (inf_le_left : latG (Wc D i) (g * a₀) ⊓ latG (Wc D i) g ≤ _)
      rw [hT]
      exact le_inf Submodule.smul_le_right h2
  have hga : latG (Wc D i) (g * a) = latG (Wc D i) (g * a₀) := by
    have := latG_mul_levG D R hL i (g * a) (a⁻¹ * a₀) hK
    rw [← this, mul_assoc, mul_inv_cancel_left]
  exact ⟨a, ha, hga.trans hTL, e, a₀, he, ha₀.2.1, hK, hTL⟩

end GlobalTheory.HeckeLatCoset
end
end
