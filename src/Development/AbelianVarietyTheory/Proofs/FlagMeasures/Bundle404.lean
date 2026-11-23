module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AtBase
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PlacesOf
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle396
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle397
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RowsConc
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle398
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.TensAll
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GramMapPreimageVolumeLowerBoundStatement
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.T2SpaceTensorProductFiniteExtension
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.Bundle009
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.FibUniq
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.TensTop
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle395
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.StabilizerDilationWeightsDualIsotropicVector
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle077
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CompactGroupHaarExists
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LintegralHermitianOrbitSumFixedLengthLtTop
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
import Mathlib.RingTheory.Coalgebra.CoassocSimps
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Compactness.Paracompact
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle018
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.Measures
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MatrixOfBesselTwoSidedAction
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle011

@[expose] public section

section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HL.TermOrbit

section Places

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E}

theorem ext_eq (A : Places F E sig) {n : ℕ} (p : IsDedekindDomain.HeightOneSpectrum (𝓞 F))
    {g : (Fin n → E) ≃ₗ[E] (Fin n → E)} {g₁ g₂ : (Fin n → (A.loc p).Ep) ≃ₗ[(A.loc p).Ep] (Fin n → (A.loc p).Ep)}
    (h₁ : A.Ext p g g₁) (h₂ : A.Ext p g g₂) : g₁ = g₂ := by
  have hb : ∀ i : Fin n, A.bc p (Pi.single i 1) = Pi.single i 1 := by
    intro i; funext j
    simp only [Places.bc, Pi.single_apply]
    split_ifs <;> simp
  apply LinearEquiv.toLinearMap_injective
  apply (Pi.basisFun (A.loc p).Ep (Fin n)).ext
  intro i
  simp only [Pi.basisFun_apply, LinearEquiv.coe_coe]
  rw [← hb i, h₁, h₂]

theorem mem_rat_inf (A : Places F E sig) {n : ℕ}
    (K K' : ∀ p, Subgroup ((Fin n → (A.loc p).Ep) ≃ₗ[(A.loc p).Ep] (Fin n → (A.loc p).Ep)))
    {g : (Fin n → E) ≃ₗ[E] (Fin n → E)} (h : g ∈ A.rat K) (h' : g ∈ A.rat K') :
    g ∈ A.rat (fun p => K p ⊓ K' p) := by
  intro p
  obtain ⟨g₁, hg₁, e₁⟩ := h p
  obtain ⟨g₂, hg₂, e₂⟩ := h' p
  obtain rfl := ext_eq A p e₁ e₂
  exact ⟨g₁, ⟨hg₁, hg₂⟩, e₁⟩

theorem rat_mono (A : Places F E sig) {n : ℕ}
    {K K' : ∀ p, Subgroup ((Fin n → (A.loc p).Ep) ≃ₗ[(A.loc p).Ep] (Fin n → (A.loc p).Ep))}
    (hK : ∀ p, K p ≤ K' p) {g : (Fin n → E) ≃ₗ[E] (Fin n → E)} (h : g ∈ A.rat K) : g ∈ A.rat K' := by
  intro p
  obtain ⟨g₁, hg₁, e₁⟩ := h p
  exact ⟨g₁, hK p hg₁, e₁⟩

end Places

end GlobalTheory.HL.TermOrbit

namespace GlobalTheory.HL.TermOrbit

section Coord

variable {D : D7} {Z : LocDat D} {T T' : D.host.E} {F0 : LFlag (D.sp.Y 0) D.R.rS T} {F0' : LFlag (D.sp.Y 0) D.R.rS T'}
  {FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS} {G : GFrames (placesOf Z) D.R.rS D.R.k}
  (c : GCoord Z F0 F0' FP G)

theorem grp_mul (ρ a b : (VS D).V ≃ₗ[D.host.E] (VS D).V) : c.grp ρ (a * b) = c.grp ρ a * c.grp ρ b := by
  ext x; simp [GCoord.grp, LinearEquiv.mul_apply]

theorem grp_one (ρ : (VS D).V ≃ₗ[D.host.E] (VS D).V) : c.grp ρ 1 = 1 := by
  ext x; simp [GCoord.grp]

theorem grp_inv (ρ a : (VS D).V ≃ₗ[D.host.E] (VS D).V) : c.grp ρ a⁻¹ = (c.grp ρ a)⁻¹ := by
  refine eq_inv_of_mul_eq_one_left ?_
  rw [← grp_mul, inv_mul_cancel, grp_one]

theorem grp_conj (ρ τ a : (VS D).V ≃ₗ[D.host.E] (VS D).V) : c.grp (ρ * τ) a = c.grp ρ (τ * a * τ⁻¹) := by
  ext x; simp [GCoord.grp, LinearEquiv.mul_eq_trans, LinearEquiv.symm_trans_apply]

theorem grp_surj (ρ : (VS D).V ≃ₗ[D.host.E] (VS D).V) (s : G.GLV) :
    c.grp ρ (((ρ.trans c.e).trans s).trans (ρ.trans c.e).symm) = s := by
  ext x; simp [GCoord.grp]

theorem lat_map_grp (ρ a σ : (VS D).V ≃ₗ[D.host.E] (VS D).V) (Λ : Submodule (𝓞 D.host.E) (VS D).V) :
    (c.lat (ρ * a) Λ).map (((c.grp ρ σ : G.GLV) : G.V →ₗ[D.host.E] G.V).restrictScalars (𝓞 D.host.E)) =
      c.lat (ρ * (σ * a)) Λ := by
  simp only [GCoord.lat]
  rw [← Submodule.map_comp]
  congr 1
  ext x; simp [GCoord.grp, LinearEquiv.mul_apply]

theorem lat_mul (ρ a : (VS D).V ≃ₗ[D.host.E] (VS D).V) (Λ : Submodule (𝓞 D.host.E) (VS D).V) :
    c.lat (ρ * a) Λ = c.lat ρ (Formalism.HermitianLatticesTheory.gmap a Λ) := by
  simp only [GCoord.lat, Formalism.HermitianLatticesTheory.gmap]
  rw [← Submodule.map_comp]
  congr 1

theorem lat_inj (ρ : (VS D).V ≃ₗ[D.host.E] (VS D).V) {Λ₁ Λ₂ : Submodule (𝓞 D.host.E) (VS D).V}
    (h : c.lat ρ Λ₁ = c.lat ρ Λ₂) : Λ₁ = Λ₂ :=
  Submodule.map_injective_of_injective
    (f := (((ρ.trans c.e : (VS D).V ≃ₗ[D.host.E] G.V) : (VS D).V →ₗ[D.host.E] G.V).restrictScalars (𝓞 D.host.E)))
    (fun x y hxy => (ρ.trans c.e).injective hxy) h

end Coord

theorem gmap_mul {D : D7} (a b : (VS D).V ≃ₗ[D.host.E] (VS D).V) (Λ : Submodule (𝓞 D.host.E) (VS D).V) :
    Formalism.HermitianLatticesTheory.gmap (a * b) Λ = Formalism.HermitianLatticesTheory.gmap a (Formalism.HermitianLatticesTheory.gmap b Λ) := by
  simp only [Formalism.HermitianLatticesTheory.gmap]
  rw [← Submodule.map_comp]
  rfl

theorem gmap_one {D : D7} (Λ : Submodule (𝓞 D.host.E) (VS D).V) : Formalism.HermitianLatticesTheory.gmap (1 : (VS D).V ≃ₗ[D.host.E] (VS D).V) Λ = Λ := by
  simp only [Formalism.HermitianLatticesTheory.gmap]
  exact Submodule.map_id Λ

end GlobalTheory.HL.TermOrbit

namespace GlobalTheory.HL.TermOrbit

theorem gterm_eq_of_rel {D : D7} {X : HidaSetting D} {u u' : D.what₂.Word}
    {F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)} {F0' : FlagG (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)}
    {what₂ rows' : Finset (Submodule (𝓞 D.host.E) (VS D).V)} {t t' : GTerm X u u' F0 F0' what₂ rows'}
    (h₁ : t.lam = t'.lam) (h₂ : t.lam' = t'.lam')
    (h : ∃ a ∈ NLam t.lam (lf D F0), ∃ b ∈ NLam t.lam' (lf D F0'), t'.lin = a * t.lin * b) : t = t' := by
  obtain ⟨l, hl, l', hl', cl⟩ := t
  obtain ⟨k, hk, k', hk', ck⟩ := t'
  simp only at h₁ h₂
  subst h₁ h₂
  obtain ⟨a, ha, b, hb, e⟩ := h
  have hc : cl = ck := by
    rw [← Quot.out_eq cl, ← Quot.out_eq ck]
    exact Quot.sound ⟨a, ha, b, hb, e⟩
  subst hc
  rfl

theorem term_eq_iff_lRel : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), Formalism.MainNotions.S.Cnt.Stand D u u' → 4 * D.R.rS + 7 ≤ D.R.k → ∀ (w : Point D.host.E (D.R.rS + 1)) (F00 : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F'0 : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (FP : ∀ p : PlF D, LocNG.FPair (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p) D.R.rS), ZhatOM (ZhatL F00 F'0) = ptMat w → Gval F00 F'0 ≠ 0 → (∀ p, AtBase (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p F00 F'0 (Tu D u) (Tu D u') (FP p) ∧ (FP p).RelG (LocNG.theta (Y.M p))) → ∀ (G : GFrames (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)) D.R.rS D.R.k) (c : GCoord (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) F00 F'0 FP G), ∀ (t₀ : TauC Y u u') (ρ : ((VS D).V ≃ₗ[D.host.E] (VS D).V)) (U U' : Formalism.L2.SG.PairVal.MatR D), MovesTo F00 F'0 (lf D (X.Fu u)) t₀.frame ρ U U' → ∀ (t t' : TauC Y u u') n m n' m', t.lam = t₀.lam → t.lam' = t₀.lam' → t'.lam = t₀.lam → t'.lam' = t₀.lam' → n ∈ NRat (lf D (X.Fu u)) ∧ m ∈ NRat (lf D (X.Fu u')) ∧ t.lin = n⁻¹ * t₀.lin * m → n' ∈ NRat (lf D (X.Fu u)) ∧ m' ∈ NRat (lf D (X.Fu u')) ∧ t'.lin = n'⁻¹ * t₀.lin * m' → (t = t' ↔ G.LRel (c.lat (ρ * n) t.lam) (c.lat (ρ * n') t'.lam)) := by
  intro D X Y u u' hst hk w F00 F'0 FP hZ hG hAt G c t₀ ρ U U' hmv t t' n m n' m' e₁ e₂ e₃ e₄ hnm hnm'
  obtain ⟨hn, hm, ht⟩ := hnm
  obtain ⟨hn', hm', ht'⟩ := hnm'
  have hI := GlobalTheory.T.rational_unipotent_groups_lattices_global_coordinates D X Y u u' hst hk w F00 F'0 FP hZ hG hAt G c t₀ ρ U U' hmv
  have hN := hI.1
  have hN' := hI.2.1
  constructor
  · rintro rfl
    have key : n' * n⁻¹ = t₀.lin * (m' * m⁻¹) * t₀.lin⁻¹ := by
      calc n' * n⁻¹ = n' * (n⁻¹ * t₀.lin * m) * m⁻¹ * t₀.lin⁻¹ := by group
        _ = n' * (n'⁻¹ * t₀.lin * m') * m⁻¹ * t₀.lin⁻¹ := by rw [← ht, ← ht']
        _ = t₀.lin * (m' * m⁻¹) * t₀.lin⁻¹ := by group
    refine ⟨c.grp ρ (n' * n⁻¹), ?_, ?_⟩
    · have h1 : c.grp ρ (n' * n⁻¹) ∈ G.N := by
        rw [grp_mul, grp_inv]
        exact G.N.mul_mem ((hN n').1 hn') (G.N.inv_mem ((hN n).1 hn))
      have h2 : c.grp ρ (n' * n⁻¹) ∈ G.N' := by
        rw [key, ← grp_conj, grp_mul, grp_inv]
        exact G.N'.mul_mem ((hN' m').1 hm') (G.N'.inv_mem ((hN' m).1 hm))
      exact mem_rat_inf _ _ _ h1 h2
    · rw [lat_map_grp]
      congr 2
      group
  · rintro ⟨s, hs, hmap⟩
    set σ := ((ρ.trans c.e).trans s).trans (ρ.trans c.e).symm with hσdef
    have hsσ : c.grp ρ σ = s := grp_surj c ρ s
    have hsN : s ∈ G.N := rat_mono _ (fun p => inf_le_left) hs
    have hsN' : s ∈ G.N' := rat_mono _ (fun p => inf_le_right) hs
    have hΛ : Formalism.HermitianLatticesTheory.gmap (σ * n) t.lam = Formalism.HermitianLatticesTheory.gmap n' t.lam := by
      rw [← hsσ, lat_map_grp, e₃, ← e₁, lat_mul, lat_mul] at hmap
      exact lat_inj c ρ hmap
    set a := n'⁻¹ * σ * n with ha_def
    set b := m⁻¹ * t₀.lin⁻¹ * σ⁻¹ * t₀.lin * m' with hb_def
    have haN : a ∈ NRat (lf D (X.Fu u)) := by
      rw [hN, ha_def, grp_mul, grp_mul, grp_inv, hsσ]
      exact G.N.mul_mem (G.N.mul_mem (G.N.inv_mem ((hN n').1 hn')) hsN) ((hN n).1 hn)
    have hσ' : c.grp (ρ * t₀.lin) (t₀.lin⁻¹ * σ * t₀.lin) = s := by
      rw [grp_conj, ← hsσ]
      congr 1
      group
    have hbN : b ∈ NRat (lf D (X.Fu u')) := by
      have eb : b = m⁻¹ * (t₀.lin⁻¹ * σ * t₀.lin)⁻¹ * m' := by rw [hb_def]; group
      rw [hN', eb, grp_mul, grp_mul, grp_inv, grp_inv, hσ']
      exact G.N'.mul_mem (G.N'.mul_mem (G.N'.inv_mem ((hN' m).1 hm)) (G.N'.inv_mem hsN')) ((hN' m').1 hm')
    have haΛ : Formalism.HermitianLatticesTheory.gmap a t.lam = t.lam := by
      rw [ha_def, mul_assoc, gmap_mul, hΛ, ← gmap_mul, inv_mul_cancel, gmap_one]
    have haΛ' : Formalism.HermitianLatticesTheory.gmap a⁻¹ t.lam = t.lam := by
      conv_lhs => rw [← haΛ]
      rw [← gmap_mul, inv_mul_cancel, gmap_one]
    have hl : Formalism.HermitianLatticesTheory.gmap t.lin t.lam' = t.lam := t.rep.2.2.2.1
    have hl' : Formalism.HermitianLatticesTheory.gmap t'.lin t'.lam' = t'.lam := t'.rep.2.2.2.1
    have eb2 : b = t.lin⁻¹ * a⁻¹ * t'.lin := by
      rw [hb_def, ha_def, ht, ht']; group
    have hbΛ : Formalism.HermitianLatticesTheory.gmap b t.lam' = t.lam' := by
      have hl'' : Formalism.HermitianLatticesTheory.gmap t'.lin t.lam' = t.lam := by rw [e₂, ← e₄, hl', e₃, e₁]
      rw [eb2, gmap_mul, gmap_mul, hl'', haΛ', ← hl, ← gmap_mul, inv_mul_cancel, gmap_one]
    refine gterm_eq_of_rel (by rw [e₁, e₃]) (by rw [e₂, e₄]) ⟨a, ⟨⟨haN.1, haΛ⟩, haN.2⟩, b, ⟨⟨hbN.1, hbΛ⟩, hbN.2⟩, ?_⟩
    rw [ht, ht', ha_def, hb_def]
    group

end GlobalTheory.HL.TermOrbit
end

section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.FourierDecayAlt Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.SnFam
open scoped Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.same_row_same_coset_scalar_corank_one : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ∀ t t' : TauC Y u u', t.G ≠ 0 → (Y.tO u u').rowOf t = (Y.tO u u').rowOf t' → nmlOf Y u u' t = nmlOf Y u u' t' → (Y.tO u u').s0 t t' = 1 ∧ (Y.tO u u').scal t t' := by
  first | exact @GlobalTheory.SnFamCoset.scalar_of_same_coset | exact GlobalTheory.SnFamCoset.scalar_of_same_coset | (intros; apply GlobalTheory.SnFamCoset.scalar_of_same_coset <;> assumption)
end

section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.FourierDecayAlt Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.SnFam
open scoped Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.scalarCorankOnePairs_trans : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ∀ t t' t'' : TauC Y u u', t.G ≠ 0 → t'.G ≠ 0 → t''.G ≠ 0 → (Y.tO u u').s0 t t' = 1 → (Y.tO u u').scal t t' → (Y.tO u u').s0 t' t'' = 1 → (Y.tO u u').scal t' t'' → (Y.tO u u').s0 t t'' = 1 ∧ (Y.tO u u').scal t t'' := by
  first | exact @GlobalTheory.ScalTrans.scalar_pair_trans | exact GlobalTheory.ScalTrans.scalar_pair_trans | (intros; apply GlobalTheory.ScalTrans.scalar_pair_trans <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures
open scoped TensorProduct ENNReal

namespace GlobalTheory.LocalFibreNonzero

open Topology Set Filter

section Gen

variable {V X Y : Type} [TopologicalSpace V] [MeasurableSpace V] [BorelSpace V] [T2Space V]
  [LocallyCompactSpace V] [SecondCountableTopology V]
  [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X] [T2Space X]
  [LocallyCompactSpace X]
  {μ : Measure V} {ν : Measure X} [IsFiniteMeasureOnCompacts μ] [IsFiniteMeasureOnCompacts ν]
  [ν.IsOpenPosMeasure]
  {f : V → Y} {ι : X → Y} {U : Set V} {fib : X → Measure V}

private theorem exists_continuous_compactSupport_bump_of_isOpen (hU : IsOpen U) {x : V} (hx : x ∈ U) :
    ∃ φ : V → ℝ, Continuous φ ∧ HasCompactSupport φ ∧ tsupport φ ⊆ U ∧ φ x = 1 ∧
      ∀ v, 0 ≤ φ v := by
  obtain ⟨O, hO, hxO, hOU, hOc⟩ :=
    exists_open_between_and_isCompact_closure isCompact_singleton hU
      (Set.singleton_subset_iff.mpr hx)
  obtain ⟨g, hgs, hg1, hg01⟩ :=
    exists_tsupport_one_of_isOpen_isClosed hO hOc isClosed_singleton hxO
  refine ⟨g, g.continuous, ?_, hgs.trans (subset_closure.trans hOU), ?_, fun v => (hg01 v).1⟩
  · exact hOc.of_isClosed_subset (isClosed_tsupport _) (hgs.trans subset_closure)
  · simpa using hg1 (Set.mem_singleton x)

theorem fib_ne_zero_of_lb (h : IsFibreFamily μ f ι U ν univ fib) (hU : IsOpen U) {f' : V → X}
    (hf' : Continuous f') (hff' : ∀ v, f v = ι (f' v)) (hι : Function.Injective ι)
    {x : V} (hx : x ∈ U) {b0 : X}
    (hlb : ∀ W : Set V, IsOpen W → x ∈ W → ∃ c : ℝ≥0∞, 0 < c ∧ c ≠ ⊤ ∧ ∃ N ∈ 𝓝 b0,
      ∀ S ⊆ N, MeasurableSet S → c * ν S ≤ μ (f ⁻¹' (ι '' S) ∩ W)) :
    fib b0 ≠ 0 := by
  intro h0
  obtain ⟨φ, hφc, hφs, hφU, hφx, hφ0⟩ := exists_continuous_compactSupport_bump_of_isOpen hU hx
  obtain ⟨hsupp, hdis, hcont⟩ := h
  obtain ⟨hint, hgc⟩ := hcont φ hφc hφs hφU

  set W : Set V := {v | (1 / 2 : ℝ) < φ v} with hW
  have hWo : IsOpen W := isOpen_lt continuous_const hφc
  have hxW : x ∈ W := by
    show (1 / 2 : ℝ) < φ x
    rw [hφx]; norm_num
  have hWU : W ⊆ U := fun v hv =>
    hφU (subset_tsupport _ (by
      show φ v ≠ 0
      exact ne_of_gt (lt_trans (by norm_num) hv)))
  obtain ⟨c, hc0, hctop, N, hN, hlbN⟩ := hlb W hWo hxW
  set e : ℝ≥0∞ := ENNReal.ofReal (1 / 2) * c with he
  have he0 : e ≠ 0 := mul_ne_zero (by simp) hc0.ne'
  have hetop : e ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top hctop
  have hepos : 0 < e.toReal := ENNReal.toReal_pos he0 hetop
  set δ : ℝ := e.toReal / 2 with hδ
  have hδpos : 0 < δ := by rw [hδ]; linarith
  have hδe : ENNReal.ofReal δ < e := by
    rw [← ENNReal.ofReal_toReal hetop, ENNReal.ofReal_lt_ofReal_iff hepos, hδ]
    linarith

  have hgcont : Continuous (fun b => ∫ v, φ v ∂(fib b)) := continuousOn_univ.mp hgc
  have hg0 : (∫ v, φ v ∂(fib b0)) = 0 := by simp [h0]
  have hnear : {b | (∫ v, φ v ∂(fib b)) < δ} ∈ 𝓝 b0 :=
    hgcont.continuousAt.preimage_mem_nhds (Iio_mem_nhds (by rw [hg0]; exact hδpos))
  obtain ⟨K, hK, hKsub, hKc⟩ := local_compact_nhds (Filter.inter_mem hN hnear)
  have hKm : MeasurableSet K := hKc.isClosed.measurableSet
  have hK0 : 0 < ν K := Measure.measure_pos_of_mem_nhds ν hK
  have hKtop : ν K ≠ ⊤ := hKc.measure_lt_top.ne

  set A : Set V := f' ⁻¹' K with hA
  have hAm : MeasurableSet A := (hKc.isClosed.preimage hf').measurableSet
  set Φ : V → ℝ≥0∞ := A.indicator (fun v => ENNReal.ofReal (φ v)) with hΦ
  have hΦm : Measurable Φ := (ENNReal.measurable_ofReal.comp hφc.measurable).indicator hAm
  have hinner : ∀ b, ∫⁻ v, Φ v ∂(fib b) =
      K.indicator (fun b => ENNReal.ofReal (∫ v, φ v ∂(fib b))) b := by
    intro b
    have hon : ∀ᵐ v ∂(fib b), v ∈ f ⁻¹' {ι b} ∩ U := ae_iff.mpr (hsupp b)
    have hae : ∀ᵐ v ∂(fib b), f' v = b := by
      filter_upwards [hon] with v hv
      apply hι
      rw [← hff']
      exact hv.1
    have hcongr : Φ =ᵐ[fib b] fun v => K.indicator (fun _ => ENNReal.ofReal (φ v)) b := by
      filter_upwards [hae] with v hv
      by_cases hb : b ∈ K
      · have hvA : v ∈ A := by rw [hA, Set.mem_preimage, hv]; exact hb
        rw [hΦ, Set.indicator_of_mem hvA, Set.indicator_of_mem hb]
      · have hvA : v ∉ A := by rw [hA, Set.mem_preimage, hv]; exact hb
        rw [hΦ, Set.indicator_of_notMem hvA, Set.indicator_of_notMem hb]
    rw [lintegral_congr_ae hcongr]
    by_cases hb : b ∈ K
    · simp only [Set.indicator_of_mem hb]
      exact (ofReal_integral_eq_lintegral_ofReal (hint b (Set.mem_univ b))
        (ae_of_all _ hφ0)).symm
    · simp [Set.indicator_of_notMem hb]
  have hupper : ∫⁻ v in U, Φ v ∂μ ≤ ENNReal.ofReal δ * ν K := by
    rw [hdis Φ hΦm]
    simp_rw [hinner]
    rw [lintegral_indicator hKm]
    calc ∫⁻ b in K, ENNReal.ofReal (∫ v, φ v ∂(fib b)) ∂ν
        ≤ ∫⁻ _ in K, ENNReal.ofReal δ ∂ν :=
          setLIntegral_mono measurable_const
            (fun b hb => ENNReal.ofReal_le_ofReal (hKsub hb).2.le)
      _ = ENNReal.ofReal δ * ν K := setLIntegral_const K _
  have hpre : f ⁻¹' (ι '' K) = A := by
    ext v
    simp only [Set.mem_preimage, Set.mem_image, hff', hA]
    constructor
    · rintro ⟨b, hb, hbv⟩
      rwa [← hι hbv]
    · intro hv
      exact ⟨_, hv, rfl⟩
  have hsub : A ∩ W ⊆ {v | ENNReal.ofReal (1 / 2) ≤ Φ v} ∩ U := by
    intro v hv
    refine ⟨?_, hWU hv.2⟩
    show ENNReal.ofReal (1 / 2) ≤ Φ v
    rw [hΦ, Set.indicator_of_mem hv.1]
    exact ENNReal.ofReal_le_ofReal hv.2.le
  have hlower : e * ν K ≤ ∫⁻ v in U, Φ v ∂μ := by
    calc e * ν K = ENNReal.ofReal (1 / 2) * (c * ν K) := by rw [he, mul_assoc]
      _ ≤ ENNReal.ofReal (1 / 2) * μ (f ⁻¹' (ι '' K) ∩ W) :=
          mul_le_mul_of_nonneg_left (hlbN K (fun b hb => (hKsub hb).1) hKm) (by positivity)
      _ ≤ ENNReal.ofReal (1 / 2) * (μ.restrict U) {v | ENNReal.ofReal (1 / 2) ≤ Φ v} := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          rw [hpre]
          exact (measure_mono hsub).trans (Measure.le_restrict_apply _ _)
      _ ≤ ∫⁻ v in U, Φ v ∂μ := mul_meas_ge_le_lintegral hΦm _
  have hle := hlower.trans hupper
  rw [mul_comm e, mul_comm (ENNReal.ofReal δ)] at hle
  exact absurd hle (not_le.mpr (ENNReal.mul_lt_mul_right hK0.ne' hKtop hδe))

end Gen

section Tens

open PI.VolStabS PI.VolStabS.TensAllW

theorem fib_tens {F E : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
    (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (hJ : ∀ i j, σ (J j i) = J i j) (a : ℕ) (R : Type) [CommRing R] [Algebra F R]
    [TopologicalSpace R] [IsTopologicalRing R] [LocallyCompactSpace R] [T2Space R]
    [SecondCountableTopology R] (hU : IsOpen {r : R | IsUnit r}) (hL : LIP R)
    (μ : Measure (Fin a → Fin M → R ⊗[F] E)) (ν : Measure (HermR R σ a))
    [μ.IsAddHaarMeasure] [ν.IsAddHaarMeasure]
    (fib : HermR R σ a → Measure (Fin a → Fin M → R ⊗[F] E))
    (h : IsFibreFamily μ (gramR R σ J) Subtype.val {X | LinearIndependent (R ⊗[F] E) X} ν
      univ fib)
    (x : Fin a → Fin M → R ⊗[F] E) (S : HermR R σ a) (hx : LinearIndependent (R ⊗[F] E) x)
    (hlb : ∀ W : Set (Fin a → Fin M → R ⊗[F] E), IsOpen W → x ∈ W →
      ∃ c : ℝ≥0∞, 0 < c ∧ c ≠ ⊤ ∧ ∃ N ∈ nhds S, ∀ T ⊆ N, MeasurableSet T →
        c * ν T ≤ μ ((gramR R σ J) ⁻¹' (Subtype.val '' T) ∩ W)) :
    fib S ≠ 0 ∧ ∀ K : Set (Fin a → Fin M → R ⊗[F] E), IsCompact K →
      K ⊆ {X | LinearIndependent (R ⊗[F] E) X} → fib S K < ⊤ := by
  have hopen : IsOpen {X : Fin a → Fin M → R ⊗[F] E | LinearIndependent (R ⊗[F] E) X} :=
    isOpen_linIndep (Module.finBasis F E) R hU hL
  refine ⟨fib_ne_zero_of_lb h hopen (f' := gramH R σ hσ J hJ) (continuous_gramH R σ hσ J hJ)
    (fun _ => rfl) Subtype.val_injective hx hlb, fun K hK hKU => ?_⟩
  exact PI.VolStabS.FibUniq.fin_cpt h hopen S K hK hKU

end Tens

theorem fibre_nonzero_finite : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (v : HeightOneSpectrum (𝓞 F)), ∀ a : ℕ, ∀ (μ : Measure (Fin a → Fin n → Fv F v ⊗[F] E)) (ν : Measure (HermR (Fv F v) σ a)), μ.IsAddHaarMeasure → ν.IsAddHaarMeasure → ∀ fib : HermR (Fv F v) σ a → Measure (Fin a → Fin n → Fv F v ⊗[F] E), IsFibreFamily μ (gramR (Fv F v) σ J) Subtype.val {X | LinearIndependent (Fv F v ⊗[F] E) X} ν Set.univ fib → ∀ (x : Fin a → Fin n → Fv F v ⊗[F] E) (S : HermR (Fv F v) σ a), LinearIndependent (Fv F v ⊗[F] E) x → gramR (Fv F v) σ J x = (S : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) → fib S ≠ 0 ∧ ∀ K : Set (Fin a → Fin n → Fv F v ⊗[F] E), IsCompact K → K ⊆ {X | LinearIndependent (Fv F v ⊗[F] E) X} → fib S K < ⊤ := by
  intro F E _ _ _ _ _ σ hCM n J hJ v a μ ν hμ hν fib h x S hx hS
  have := PI.VolStabS.secondCountable_Fv F v
  have := PI.VolStabS.locallyCompact_Fv F v
  have : FiniteDimensional F E :=
    Module.finite_of_finrank_pos (by rw [hCM.2.2.1]; norm_num)
  have hσ : ∀ y, σ (σ y) = y := PI.VolStabS.sigma_invol σ hCM.2.2.2
  exact fib_tens σ hσ J hJ.1 a (Fv F v) (PI.VolStabS.isOpen_units_Fv F v)
    (PI.VolStabS.TensAllW.lip_field _) μ ν fib h x S hx
    (GlobalTheory.T.gramMap_preimage_volume_lower_bound F E σ hCM n J hJ v a μ ν hμ hν x S hx hS)

end GlobalTheory.LocalFibreNonzero
end

section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

theorem _root_.GlobalTheory.T.haarLie_isHaarOn_unipotentRadical : ∀ (k r : ℕ) (κ : ENNReal), 0 < κ → κ < ⊤ → IsHaarOn (Nset k r) (haarLie (Nset k r) κ) := by
  first | exact @GlobalTheory.haarLie_isHaarOn_Nset | exact GlobalTheory.haarLie_isHaarOn_Nset | (intros; apply GlobalTheory.haarLie_isHaarOn_Nset <;> assumption)
end

section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal
open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S BranchingSupport GlobalTheory.CellAmp
namespace GlobalTheory.NConjHaar

theorem map_conj_eq_smul : ∀ (k r : ℕ) (L : Formalism.MainNotions.S.LocBessel k r), 0 < L.κN → L.κN ≠ ⊤ → ∀ a : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ, a ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) → (∀ n, n ∈ Formalism.QuantumDeterminants.Nset k r ↔ a * n * a⁻¹ ∈ Formalism.QuantumDeterminants.Nset k r) → ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ L.μN.map (Formalism.QuantumDeterminants.conjM a) = C • L.μN := by
  intro k r L h0 ht a ha hN
  have hμ := GlobalTheory.haarLie_isHaarOn_Nset k r L.κN h0 ht.lt_top
  have hu : IsUnit a.det := GlobalTheory.Amp.StabHaar.unit_of_GG ha
  have hmap := GlobalTheory.Amp.StabHaar.haar_conj (G := Formalism.QuantumDeterminants.Nset k r) (G' := Formalism.QuantumDeterminants.Nset k r) a hu hN hμ
  obtain ⟨c, c0, ct, hc⟩ := GlobalTheory.BesselPeriodCompare.haar_unique (Formalism.FourierDecayAlt.P.B2x2.closedN k r) hmap hμ
  exact ⟨c, ct, hc⟩

end GlobalTheory.NConjHaar
end

section

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice
open scoped TensorProduct ENNReal

theorem _root_.GlobalTheory.T.lintegral_hermitian_orbit_sum_fixed_length_lt_top : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (β : F), β ≠ 0 → ∀ Φ : (Fin 1 → Fin M → AF F ⊗[F] E) → ℂ, Continuous Φ → HasCompactSupport Φ → ∀ (μ : Measure (HA (AF F) σ J)) (𝓕 : Set (HA (AF F) σ J)), μ.IsHaarMeasure → IsFundamentalDomain (HFinIn (AF F) σ J) 𝓕 μ → ∫⁻ h in 𝓕, ∑' x : {x : Fin 1 → Fin M → E | hE σ J (x 0) (x 0) = algebraMap F E β}, ‖Φ (h⁻¹ • ratTup (F := F) (AF F) (x : Fin 1 → Fin M → E))‖ₑ ∂μ < ⊤ := by
  first | exact @GlobalTheory.OrbitSumInt.lintegral_orbitSum_lt_top | exact GlobalTheory.OrbitSumInt.lintegral_orbitSum_lt_top | (intros; apply GlobalTheory.OrbitSumInt.lintegral_orbitSum_lt_top <;> assumption)
end
