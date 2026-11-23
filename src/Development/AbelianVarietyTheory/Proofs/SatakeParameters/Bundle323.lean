module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle017
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsMidLevIff
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle317
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle024
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle155
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle245
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle307
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle161
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle160
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.KerHypAll
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle025
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DualLatticeLocalCharacterization
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle319
public import Formalism.LocalToGlobal.GlobalTheory.GL6.PBwLocBases
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle008
public import Formalism.SharpRestriction.GrowthBounds.IntegralWeylLatticeSpan.LatSOfLocBasis
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle309
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle310
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
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle016
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle005

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.UG Formalism.L2.DIV Formalism.L2.G.Pend Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct

noncomputable section

namespace GlobalTheory.TwV.Xc

theorem latK_rat_mul_lev : letI := fun D : D7 => D.host.cmStar; ∀ (D : D7) (N : ℕ) (J : Matrix (Fin N) (Fin N) D.host.E) (T f : ℕ) (bad : Set (HeightOneSpectrum (𝓞 D.host.F))) (S : StepLevel D.host.F D.host.E (sigD D) J T f bad) (a : 𝓞 D.host.E) (x : GL (Fin N) (AfE D.host.F D.host.E)) (κ : S.U), ∀ g ∈ UJ (sigD D : D.host.E →+* D.host.E) J, latK D.sp J a (GlobalTheory.TwU.ratA D.host.F g * x * κ.1) S.Lb = SDLat.smulLat (eMat rfl (D.sp.cm.sig : D.host.E →+* D.host.E) J g) (latK D.sp J a x S.Lb) := by
  intro D N J T f bad S a x κ g hg
  letI := D.host.cmStar
  rw [Formalism.MainNotions.G.KAat.latK_tr _ _ _ _ _ g hg (GlobalTheory.TwU.hatStab_of_lev S κ)]
  unfold SDLat.smulLat eMat
  congr 1
  ext v
  simp [Matrix.toLin'_toMatrix']

end GlobalTheory.TwV.Xc

end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Forms Formalism.L2.Col Formalism.L2.DIV Formalism.HermitianLatticesTheory GlobalTheory.KerJ NumberField IsDedekindDomain Classical

namespace GlobalTheory.KerJ

theorem gmap_of_fix {X : Fields} {n : ℕ} {ST SG Q : Finset (HeightOneSpectrum (𝓞 X.E))} {Λ : LevFam X.E X.K n SG}
    {Θ : LevQFam X.E X.K n Q} (a : FrmG Λ Θ) (p : DecoF X.E n ST SG Q) (h : a • p = p) :
    gmap a.1.1 p.deco.1.N = p.deco.1.N :=
  congrArg (fun q : DecoF X.E n ST SG Q => q.deco.1.N) h

theorem mulLat_mul_le {E : Type} [Field E] [NumberField E] {H : Type} [AddCommGroup H] [Module (𝓞 E) H] (a b : ℕ)
    (M : Submodule (𝓞 E) H) : mulLat (a * b) M ≤ mulLat b M := by
  rintro z ⟨w, hw, rfl⟩
  refine ⟨((a : 𝓞 E)) • w, M.smul_mem _ hw, ?_⟩
  simp only [LinearMap.smul_apply, LinearMap.id_apply, smul_smul, Nat.cast_mul, mul_comm]

theorem term_law : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (K : G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Y cX) (t : KerEntTied ex), ColSide t → ∀ u μ (G : StabDat (D.chTw u μ)), StabPin t u μ G → ∀ i < D.R.m, ∀ c c', ∀ g ∈ G (i + 1) c', TermLaw (t.O u μ) i c c' g := by
  intro D L hT Gi Gl K Y cX ex t hC u μ G hG i hi c c' g hg
  have hok := t.idx_ok μ
  have hm := hok.hm
  obtain ⟨hSS, hlev, -⟩ := t.rd_chain u μ
  obtain ⟨pt, ix, yb, pT, hN, hyb, hE, hC1, hTop, hGi, hGm, hGT⟩ := hG
  have dat := GlobalTheory.T.pairKernelLaw_of_finiteDatumLaw D L hT Gi Gl K Y cX ex t hC.fields hC.sel hC.bad.1 hC.bad.2.1 hC.bad.2.2.1 hC.bad.2.2.2 hC.chars u μ i hi c c'
  have fin : ∀ (f : HomE t.X.E (D.R.N i) (D.R.N (i + 1)) → t.X.K) (N : Submodule (𝓞 t.X.E) (Sp t.X.E (D.R.N i)))
      (N' : Submodule (𝓞 t.X.E) (Sp t.X.E (D.R.N (i + 1)))) (γ : UF t.X.E (D.R.N (i + 1))) (k : t.X.K),
      (t.rd u μ).N i c = N → (t.rd u μ).N (i + 1) c' = N' → (∀ x, (t.rd u μ).Xi i c c' x = t.seam.σ₀ (f x)) →
      gmap γ.1 N' = N' →
      (∀ x z, z ∈ mulLat (cBof t.sel (t.tup μ) (t.cst μ) (t.word u)) (homAt (Sall t.sel (t.tup μ) (t.word u)) N N') → f (x + z) = f x) →
      (∀ x, f (γ.1.toLinearMap ∘ₗ x) * ∏ P : rowSG t.Pr t.sel (t.tup μ), muAt t.Ch t.sel (t.tup μ) (t.cst μ) i P ((LinearEquiv.det γ.1 : t.X.Eˣ) : t.X.E) = k * f x) →
      TermLaw (t.O u μ) i c c' (matE t.seam γ.1, t.seam.σ₀ k) := by
    intro f N N' γ k hN1 hN2 hf hγ hinv hlaw
    subst hN1 hN2
    refine dat γ k hγ (fun x z hz => ?_) fun x => ?_
    · rw [hlev, hSS] at hz
      rw [hf, hf, hinv x z (mulLat_mul_le _ _ _ hz)]
    · rw [hf, hf, ← map_mul, ← map_mul, hlaw]
  rcases lt_trichotomy i t.m2 with hlt | heq | hgt
  · rw [hGi (i + 1) (by omega) (by omega) c'] at hg
    obtain ⟨a, hfix, -, rfl⟩ := hg
    exact fin _ _ _ a.1 _ (hN i (by omega) c) (hN (i + 1) (by omega) c') (hE i hlt c c') (gmap_of_fix a _ hfix)
      (fun x z hz => xiEntry_invA t.Ch t.sel (t.tup μ) (t.cst μ) (t.idx μ) t.pr_ok hok i hlt _ _ _ _ x z hz)
      (GlobalTheory.FiLaw.xiEntry_stab t.Ch t.sel (t.tup μ) (t.cst μ) (t.idx μ) t.glob t.m2 hC.fields t.pr_ok hC.sel hC.bad.1 hC.bad.2.1 hok hC.chOk
        (hC.sharp μ) (hC.deep μ).1 (hC.repOne μ) (t.word u) i hlt _ _ _ _ a hfix)
  · subst heq
    obtain ⟨b, -⟩ := hok.last_uniq
    rw [hGm b c'] at hg
    obtain ⟨a, hfix, hY, rfl⟩ := hg
    exact fin _ _ _ a.1 _ (hN _ (Nat.le_succ _) c) (hN _ le_rfl c') (hC1 c c') (gmap_of_fix a _ hfix)
      (fun x z hz => xiCpl1_invA t.Ch t.sel (t.tup μ) (t.cst μ) (t.idx μ) t.pr_ok hok _ _ _ _ x z hz)
      (GlobalTheory.StabLaw.xiCpl1_stab t.Ch t.sel (t.tup μ) (t.cst μ) (t.idx μ) t.glob _ hC.fields t.pr_ok hC.sel hC.bad.1 hC.bad.2.1 hok hC.chOk
        (hC.sharp μ) (hC.deep μ).1 (hC.repOne μ) (t.word u) _ b _ _ _ a (hyb c') hfix hY)
  · have hi' : i = t.m2 + 1 := by omega
    subst hi'
    rw [hGT c'] at hg
    obtain ⟨a, hfix, -, rfl⟩ := hg
    exact fin _ _ _ a.1 _ (hN _ le_rfl c) (hTop.1 c') (hTop.2 c c') (gmap_of_fix a _ hfix)
      (fun x z hz => GlobalTheory.T.lastStep_datum_invariant_cB_hom_twist_primes t.Ch t.sel (t.tup μ) (t.cst μ) (t.idx μ) t.glob t.m2 hC.fields t.pr_ok hC.sel hC.bad.1 hC.bad.2.1 hok
        (t.word u) _ _ _ x z (hyb c) hz)
      (GlobalTheory.T.lastStepDatum_law_topLevelStabilizer t.Ch t.sel (t.tup μ) (t.cst μ) (t.idx μ) t.glob t.m2 hC.fields t.pr_ok hC.sel hC.bad.1 hC.bad.2.1 hok hC.chOk
        (hC.sharp μ) (hC.deep μ).1 (hC.repOne μ) (hC.deep μ).2 (t.word u) _ _ _ a (hyb c) hfix)

end GlobalTheory.KerJ
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV
open Formalism.UG (bc prV)
open Matrix Formalism.UG Formalism.L2.PairingIndexBounds.F Formalism.L2.Forms Formalism.MainNotions.G.KAat
open scoped TensorProduct

namespace GlobalTheory.ZDual

section Gen
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] {N : ℕ}

theorem pullV_dual_mem_latS_gen (σ : E →ₐ[F] E) (J : Matrix (Fin N) (Fin N) E) (hJ : IsUnit J.det)
    (Lb : Submodule (𝓞 E) (Fin N → E)) (hfin : Module.Finite (𝓞 E) Lb)
    (hspan : Submodule.span E (Lb : Set (Fin N → E)) = ⊤)
    (x : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (hx : x ∈ UPts σ J (FiniteAdeleRing (𝓞 F) F))
    (v : HeightOneSpectrum (𝓞 F)) (l : Fin N → E) (hl : l ∈ dualSet (σ : E →+* E) J (latAd x Lb)) :
    (fun k => prV (E := E) v (pullV (F := F) x l k)) ∈ latS (F := F) (v.adicCompletion F) (intV E v)
        (Submodule.span (𝓞 E) (dualSet (σ : E →+* E) J Lb)) := by
  have hU : cT (sigR σ (v.adicCompletion F)) (bc (prV (E := E) v) x).val *
      J.map (inclE (F := F) (v.adicCompletion F)) * (bc (prV (E := E) v) x).val =
      J.map (inclE (F := F) (v.adicCompletion F)) := Formalism.UG.P.afsplit_bc_mem σ J v x hx
  have hy : (fun k => prV (E := E) v (pullV (F := F) x l k)) =
      ((bc (prV (E := E) v) x)⁻¹).val *ᵥ (fun k => inclE (F := F) (v.adicCompletion F) (l k)) := by
    rw [GlobalTheory.LocCarry.coe_bc_inv]
    funext k
    unfold pullV
    rw [RingHom.map_mulVec]
    rfl
  rw [hy]
  refine GlobalTheory.St.G.Dual.bwd_loc σ J hJ.ne_zero Lb ⟨hfin, hspan⟩ v _ fun b hb => ?_
  unfold GlobalTheory.St.G.hR
  have key := Formalism.UG.P.hform_mulVec (sigR σ (v.adicCompletion F)) (J.map (inclE (F := F) (v.adicCompletion F)))
    (bc (prV (E := E) v) x).val (fun k => inclE (F := F) (v.adicCompletion F) (b k))
    (((bc (prV (E := E) v) x)⁻¹).val *ᵥ (fun k => inclE (F := F) (v.adicCompletion F) (l k)))
  rw [hU, Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec] at key
  rw [← key]
  refine Formalism.L2.G.RelativeIndexFlags.pair_int v σ J (latAd x Lb) l hl _ ?_
  rw [GlobalTheory.LocCarry.mem_latS_latAd_iff x Lb hfin hspan v, Matrix.mulVec_mulVec, ← Units.val_mul,
    inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
  exact Submodule.subset_span ⟨b, hb, rfl⟩

end Gen


attribute [local instance] Formalism.BasicNotions.Host.cmStar in
theorem pullV_dual_mem_latS : ∀ {D : D7} (i : ℕ) (hi : i ≤ D.R.m) {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 D.host.F))}
    (lev : StepLevel D.host.F D.host.E (sigD D) (gramN D i hi) T f bad) (x : UA D i hi) (v : HeightOneSpectrum (𝓞 D.host.F))
    (l : Fin (D.R.N i) → D.host.E), l ∈ dualSet (sigD D : D.host.E →+* D.host.E) (gramN D i hi) (latAd x.1 lev.Lb) →
    (fun k => prV (E := D.host.E) v (pullV (F := D.host.F) x.1 l k)) ∈ latS (F := D.host.F) (v.adicCompletion D.host.F) (intV D.host.E v)
        (Submodule.span (𝓞 D.host.E) (dualSet (sigD D : D.host.E →+* D.host.E) (gramN D i hi) lev.Lb)) := by
  intro D i hi T f bad lev x v l hl
  exact pullV_dual_mem_latS_gen (sigD D) (gramN D i hi) (Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.bwB_gramN_det D i hi) lev.Lb lev.Lb_fin
    lev.Lb_span x.1 x.2 v l hl

end GlobalTheory.ZDual
end

section

open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.L2.Col Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.L2.Ker Formalism.MainNotions Formalism.L2.DIV Formalism.MainNotions.G GlobalTheory.TwU GlobalTheory.TwV
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.chartBaseCoset_bounded_typePrimes_and_twist : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => ∀ (hi : t.m2 + 1 ≤ D.R.m) (β : (St (t.m2 + 1) hi).Ch) (P : SB t μ)
  (y : Sp t.X.E (D.R.N (t.m2 + 1))), SameCoset t.sel (t.tup μ) (t.cst μ) P y (y0At A (t.m2 + 1) hi β P) →
  (P.1 ∈ t.Pr.vGs → ∀ l, IntAt P.1 ((qOf P.1 : t.X.E) * y l)) ∧
  (P.1 ∉ t.Pr.vGs → ∀ l, IntAt P.1 ((qOf P.1 : t.X.E) ^ (t.cst μ).M * y l))) := by
  first | exact @GlobalTheory.TwV.cplCoset_bound | exact GlobalTheory.TwV.cplCoset_bound | (intros; apply GlobalTheory.TwV.cplCoset_bound <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.UG Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV Formalism.L2.Forms Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat GlobalTheory.TwU GlobalTheory.TwV
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.kernelLattice_translate_eq_image_classLattice : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => ∀ i (hi : i ≤ D.R.m) c (x : UA D i hi), ∀ γ ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D i hi), ∀ (κ : ((St i hi).K ((St i hi).chOf c)).lev.U), x.1 = ratA D.host.F γ * ((St i hi).y c).1 * κ.1 → latK D.sp (gramN D i hi) a x.1 ((St i hi).K ((St i hi).chOf c)).lev.Lb = SDLat.smulLat (LinearMap.toMatrix' ((toStdCo (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D i hi) (A.crd i hi)).trans (stdG (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D i hi) γ)).toLinearMap) (t.seam.lat ((t.rd u μ).N i c))) := by
  first | exact @GlobalTheory.TwV.latK_lev_rat | exact GlobalTheory.TwV.latK_lev_rat | (intros; apply GlobalTheory.TwV.latK_lev_rat <;> assumption)
end

section

open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.MainNotions.G GlobalTheory.TwU GlobalTheory.TwV

theorem _root_.GlobalTheory.T.orthonormalChange_intertwines_rationalIsometries : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a =>
    ∀ i (hi : i + 1 ≤ D.R.m) (γ : GL (Fin (D.R.N i)) D.host.E) (γ' : GL (Fin (D.R.N (i + 1))) D.host.E)
      (g : UF t.X.E (D.R.N i)) (g' : UF t.X.E (D.R.N (i + 1))),
      seamGL t.seam g.1 = A.crd i (Nat.le_of_succ_le hi) * γ * (A.crd i (Nat.le_of_succ_le hi))⁻¹ →
      seamGL t.seam g'.1 = A.crd (i + 1) hi * γ' * (A.crd (i + 1) hi)⁻¹ → ∀ z : HomE D.host.E (D.R.N i) (D.R.N (i + 1)),
      seamHom t.seam (inFr
        (toStdCo (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D i (Nat.le_of_succ_le hi)) (A.crd i (Nat.le_of_succ_le hi)))
        (toStdCo (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D (i + 1) hi) (A.crd (i + 1) hi)) z) =
      g'.1.toLinearMap ∘ₗ seamHom t.seam (inFr
        (toStdCo (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D i (Nat.le_of_succ_le hi)) (A.crd i (Nat.le_of_succ_le hi)))
        (toStdCo (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D (i + 1) hi) (A.crd (i + 1) hi))
        (inFr (stdG (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D i (Nat.le_of_succ_le hi)) γ)
          (stdG (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D (i + 1) hi) γ') z)) ∘ₗ g.1.symm.toLinearMap) := by
  first | exact @GlobalTheory.TwV.seamHom_inFr_stdG | exact GlobalTheory.TwV.seamHom_inFr_stdG | (intros; apply GlobalTheory.TwV.seamHom_inFr_stdG <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV
open Formalism.UG (bc prV)
open Matrix Formalism.UG Formalism.L2.PairingIndexBounds.F Formalism.L2.Forms Formalism.MainNotions.G.KAat
open scoped TensorProduct

theorem _root_.GlobalTheory.T.placeComponent_pullback_latticeVector_mem_dual_span : ∀ {D : D7} (i : ℕ) (hi : i ≤ D.R.m) {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 D.host.F))}
    (lev : StepLevel D.host.F D.host.E (sigD D) (gramN D i hi) T f bad) (x : UA D i hi) (v : HeightOneSpectrum (𝓞 D.host.F))
    (l : Fin (D.R.N i) → D.host.E), l ∈ latAd x.1 lev.Lb →
    (fun k => prV (E := D.host.E) v (pullV (F := D.host.F) x.1 l k)) ∈ latS (F := D.host.F) (v.adicCompletion D.host.F) (intV D.host.E v)
        (Submodule.span (𝓞 D.host.E) (dualSet (sigD D : D.host.E →+* D.host.E) (gramN D i hi) lev.Lb)) := by
  first | exact @GlobalTheory.AwayLat.prV_pullV_mem_latS_dual | exact GlobalTheory.AwayLat.prV_pullV_mem_latS_dual | (intros; apply GlobalTheory.AwayLat.prV_pullV_mem_latS_dual <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV

theorem _root_.GlobalTheory.T.couplingCoset_eq_chartPointCoset : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => ∀ c, cosetOf A (t.m2 + 1) (cpl_lt t μ).le ((St _ (cpl_lt t μ).le).chOf c) (A.pt _ (cpl_lt t μ).le c) = A.yb c) := by
  first | exact @GlobalTheory.TwV.cosetOf_eq_yb | exact GlobalTheory.TwV.cosetOf_eq_yb | (intros; apply GlobalTheory.TwV.cosetOf_eq_yb <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.UG Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV Formalism.L2.Forms Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat GlobalTheory.TwU GlobalTheory.TwV
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.determinantIdealCharacter_classLattice_eq : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => (∀ (N : ℕ) (M M' : SDLat D.host.E N), ∀ g ∈ Formalism.L2.Herm.UstdAf D.sp.cm N, Formalism.L2.Herm.Carries g M.1 M'.1 → ∀ y : Formalism.L2.Herm.unitaryOneFiniteAdeles D.sp.cm, Formalism.L2.Herm.IsDetOf D.sp.cm y g → D.relDet N M M' = QuotientGroup.mk (dtU y)) → (∀ i hi β, latCo D.sp (gramN D i hi) (A.crd i hi) a 1 ((St i hi).K β).lev.Lb = StandardLatticesGL3.stdL D (D.R.N i)) → ∀ i (hi : i ≤ D.R.m) c, t.χ (TaylorLogMetric.detId D (StandardLatticesGL3.stdL D _) (t.seam.lat ((t.rd u μ).N i c))) = ((D.chiD ((t.O u μ).dt i c) : ℂˣ) : ℂ)) := by
  first | exact @GlobalTheory.TwV.chi_detId_lat | exact GlobalTheory.TwV.chi_detId_lat | (intros; apply GlobalTheory.TwV.chi_detId_lat <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV

theorem _root_.GlobalTheory.T.firstCoupledStep_level_local_elements_values : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a =>
  ∀ (hi : t.m2 < D.R.m) (β : (St t.m2 hi.le).Ch) (κ : ((St t.m2 hi.le).K β).lev.U),
    ∃ (g : SB t μ → (Sp t.X.E (D.R.N t.m2) ≃ₗ[t.X.E] Sp t.X.E (D.R.N t.m2))) (z : SB t μ → t.X.K),
      (∀ P, A.midRel t.m2 hi β P (g P) (z P) ∧ InFrame t.seam (A.fb t.m2 hi.le β) (t.cst μ).D P κ.1 (g P)) ∧
      ((((St t.m2 hi.le).K β).lev.chi κ : ℂˣ) : ℂ) * t.seam.σ₀ (∏ P, z P) = 1) := by
  first | exact @GlobalTheory.TwV.levSrc_localData | exact GlobalTheory.TwV.levSrc_localData | (intros; apply GlobalTheory.TwV.levSrc_localData <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV

theorem _root_.GlobalTheory.T.kernelChainCharacter_normOne_eq_infinityType : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => ∀ i (hi : i < D.R.m), ∃ e : D.what₂.Tau → ℤ, (∀ τ, ((e τ : ℤ) : ℚ) = (D.hc τ).e ⟨i, hi⟩) ∧ ∀ z : D.host.Eˣ, (z : D.host.E) * D.host.conj (z : D.host.E) = 1 → ∀ y : (letI := D.host.cmStar; Formalism.L2.Herm.unitaryOneFiniteAdeles D.sp.cm), Matrix.GeneralLinearGroup.det y.1 = ratId D.host.F D.host.E z → (((t.O u μ).mt (i + 1) (dtU y) : ℂˣ) : ℂ) = ∏ τ, TaylorLogMetric.embT D τ (z : D.host.E) ^ e τ) := by
  first | exact @GlobalTheory.TwV.mt_ratId | exact GlobalTheory.TwV.mt_ratId | (intros; apply GlobalTheory.TwV.mt_ratId <;> assumption)
end

section

open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.MainNotions.G GlobalTheory.TwU GlobalTheory.TwV

theorem _root_.GlobalTheory.T.pointLattice_moved_rational_isometry : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a =>
    ∀ i (hi : i ≤ D.R.m) (β : (St i hi).Ch) (x x₁ : UA D i hi) (γ : GL (Fin (D.R.N i)) D.host.E),
      γ ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D i hi) → x₁.1 = ratA D.host.F γ * x.1 →
      ∀ g : UF t.X.E (D.R.N i), seamGL t.seam g.1 = A.crd i hi * γ * (A.crd i hi)⁻¹ →
      ∀ p, IsPtAd A a i hi β x p → t.seam.lat ((((g, 1, 1) : UF t.X.E (D.R.N i) × GLG (E := t.X.E) (n := D.R.N i) (SG := t.Pr.vGs) × GLQ t.X.E (D.R.N i) (QE t.sel (t.tup μ : Chr t.X.F t.X.E t.X.K))) • p)).deco.1.N = latCo D.sp (gramN D i hi) (A.crd i hi) a x₁.1 ((St i hi).K β).lev.Lb) := by
  first | exact @GlobalTheory.TwLatRat.lat_moved | exact GlobalTheory.TwLatRat.lat_moved | (intros; apply GlobalTheory.TwLatRat.lat_moved <;> assumption)
end
