module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle026
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle215
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle302
public import Formalism.SharpRestriction.Divisibility.ProductZerothFirstParts
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsMidLevIff
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle326
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChartPointRightTranslateByLevelCoupledStep
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ReadsMove
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle076
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InclMulInvMul
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsFiniteClass
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle002
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle327
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelThetaAdmissibleLattices
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle328
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.AlternatingFormStandardHermitian
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle009
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle325
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
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle025
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.RedPEqZeroOfDiv
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle003
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle022
import Formalism.AlgebraicWeights.IsAlgWeight
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import ReciprocityTheory.Automorphisms.PlaceA

@[expose] public section

section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory



theorem joint_dt_eq_det_of_isPt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Dx cX} (t : KerEntTied ex) {u : D.what₂.Word} {μ : D.what₂.Tup} {w : D.what₂.places.Pl} {hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Lv : Levels (Gl.Fl u w hg)} {I : CmpJIn ex.tw u μ w hg Lv} {H : CmpJHyp ex.cmp I} {X : LabIn I} [Fact (D.what₂.places.resChar w).Prime] (std : Lt.StdAtW D Gl u w hg) (J : Joint t H X), ∀ j (hj : j ≤ D.R.m) (La : (sysS H X std).Lt j) x, J.IsPt std j hj La x → (J.fd std).dt j La = Matrix.GeneralLinearGroup.det x.1 := by
  intro D L hT Gi Gl Kc Dx cX ex t u μ w hg Lv I H X _ std J j hj La x hx
  obtain ⟨hr, hx⟩ := hx
  have h1 : (J.fd std).dt j La = Matrix.GeneralLinearGroup.det ((J.cp std).y j La) := rfl
  rw [h1, hx]
  exact ((reindex_rename_point_det_latK D.sp hr 0 0 ((J.cp std).y j La) ⊥).2.1).symm

end GlobalTheory
end

section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.KerSiteSelfDual

theorem isSDLat_of_heq {E : Type} [Field E] [NumberField E] [StarRing E] {n N : ℕ} (h : n = N)
    {L : Submodule (𝓞 E) (Fin n → E)} {M : Submodule (𝓞 E) (Fin N → E)} (hL : HEq L M) (hM : Formalism.BasicNotions.IsSDLat E N M) :
    Formalism.BasicNotions.IsSDLat E n L := by
  subst h
  cases hL
  exact hM



theorem even_and_isSDLat_kerN : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Dx cX} (t : KerEntTied ex) {u : D.what₂.Word} {μ : D.what₂.Tup} {w : D.what₂.places.Pl} {hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Lv : Levels (Gl.Fl u w hg)} {I : CmpJIn ex.tw u μ w hg Lv} {H : CmpJHyp ex.cmp I} {X : LabIn I} [Fact (D.what₂.places.resChar w).Prime] (std : Lt.StdAtW D Gl u w hg) (J : Joint t H X), J.Dict std → ∀ j, j ≤ D.R.m → ∀ La : (sysS H X std).Lt j, ((sysS H X std).Pj j).IsLatTup La.2 → Even (((sysS H X std).Pj j).m + 1) ∧ IsSDLat D.host.E (((sysS H X std).Pj j).m + 1) ((J.fd std).kerN j La) := by
  intro D L hT Gi Gl Kc Dx cX ex t u μ w hg Lv I H X _ std J hD j hj La hLa
  obtain ⟨⟨hr, -⟩, -, hk, -⟩ := hD j hj La hLa
  refine ⟨hr ▸ Formalism.MainNotions.product_zeroth_first_parts.N_even D.R j, isSDLat_of_heq hr hk ?_⟩
  exact GlobalTheory.KerSelfDual.isSDLat_latK_of_stdL ((J.St j hj).K (J.chart std j hj La)).lev (J.A.crd j hj) J.a
    (J.pins.crd_orth j hj) (J.base j hj _) (J.pt std j hj La)

end GlobalTheory.KerSiteSelfDual
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV Formalism.UG Formalism.L2.PairingIndexBounds.F
open scoped TensorProduct


theorem _root_.GlobalTheory.T.companionLatticeVector_local_mem_dualBaseCompletion : ∀ {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] {N : ℕ}
    (sp : Spaces R F E) (J : Matrix (Fin N) (Fin N) E) (crd : GL (Fin N) E) (a : 𝓞 E)
    (x : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)), x ∈ UPts sp.cm.sig J (FiniteAdeleRing (𝓞 F) F) → IsUnit J.det →
    ∀ (Lb : Submodule (𝓞 E) (Fin N → E)), Module.Finite (𝓞 E) Lb → Submodule.span E (Lb : Set (Fin N → E)) = ⊤ →
    (∀ y ∈ Lb, y ∈ dualSet (sp.cm.sig : E →+* E) J Lb) →
    ∀ (v : HeightOneSpectrum (𝓞 F)) (u : Fin N → E), u ∈ latCo sp J crd a x Lb →
    ∃ z : latS (F := F) (v.adicCompletion F) (intV E v) (Submodule.span (𝓞 E) (dualSet (sp.cm.sig : E →+* E) J Lb)),
      z.1 = fun l => prV (E := E) v (pullV (F := F) (ratA F crd * x) u l) := by
  first | exact @GlobalTheory.CompanLocal.mem_latS_dual_of_mem_latCo | exact GlobalTheory.CompanLocal.mem_latS_dual_of_mem_latCo | (intros; apply GlobalTheory.CompanLocal.mem_latS_dual_of_mem_latCo <;> assumption)
end

section

open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.L2.Col Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.L2.Ker Formalism.MainNotions Formalism.L2.DIV Formalism.MainNotions.G GlobalTheory.TwU GlobalTheory.TwV
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.L2.Col GlobalTheory.TwU Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat
open scoped TensorProduct


theorem _root_.GlobalTheory.T.pulledLatticeVector_mem_dualBaseLatticeCompletion : ∀ {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
    (sp : Spaces R F E) {N : ℕ} (J : Matrix (Fin N) (Fin N) E), IsUnit J.det → ∀ (c : GL (Fin N) E) (a : 𝓞 E)
    (x : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)), x ∈ UPts sp.cm.sig J (FiniteAdeleRing (𝓞 F) F) →
    ∀ (Lb : Submodule (𝓞 E) (Fin N → E)), Module.Finite (𝓞 E) Lb → Submodule.span E (Lb : Set (Fin N → E)) = ⊤ →
    (∀ y ∈ Lb, y ∈ dualSet (sp.cm.sig : E →+* E) J Lb) → ∀ (v : HeightOneSpectrum (𝓞 F)) (y : Fin N → E),
    y ∈ latCo sp J c a x Lb →
    (fun l => prV (E := E) v (pullV (F := F) (ratA F c * x) y l)) ∈
      latS (F := F) (v.adicCompletion F) (intV E v) (Submodule.span (𝓞 E) (dualSet (sp.cm.sig : E →+* E) J Lb)) := by
  first | exact @GlobalTheory.MemDual.mem_latS_dual_of_latCo | exact GlobalTheory.MemDual.mem_latS_dual_of_latCo | (intros; apply GlobalTheory.MemDual.mem_latS_dual_of_latCo <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.UG Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV Formalism.L2.Forms Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat GlobalTheory.TwU GlobalTheory.TwV
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TwU.SeamKer

open Formalism.L2.Th1.H

variable {D : D7} {X : Fields}

def seamT (s : Seam D X) (a b : ℕ) : VV D.what₂.Tau a b ≃+ VV X.Tau a b where
  toFun v := fun τ => v (s.iT τ)
  invFun w := fun τ => w (s.iT.symm τ)
  left_inv v := by funext τ; simp
  right_inv w := by funext τ; simp
  map_add' _ _ := rfl

theorem HV_seamT (s : Seam D X) {a b : ℕ} (sc : ℝ) (x y : VV D.what₂.Tau a b) :
    HV sc (seamT s a b x) (seamT s a b y) = HV sc x y := by
  show (sc : ℂ) * (∑ τ, ∑ i, ∑ j, x (s.iT τ) i j * (starRingEnd ℂ) (y (s.iT τ) i j)) =
    (sc : ℂ) * ∑ τ, ∑ i, ∑ j, x τ i j * (starRingEnd ℂ) (y τ i j)
  rw [Equiv.sum_comp s.iT (fun τ' => ∑ i, ∑ j, x τ' i j * (starRingEnd ℂ) (y τ' i j))]

theorem alV_seamT (s : Seam D X) {a b : ℕ} (d : ℕ) (sc : ℝ) (x : VV D.what₂.Tau a b) :
    alV d sc (seamT s a b x) = alV d sc x := by
  have h := HV_seamT s sc x x
  simp only [alV, alphaQ, Formalism.L2.Th1.H.qOf, h]

theorem seam_kerTh : ∀ {D : D7} {X : Fields} (s : Seam D X), s.Ok → ∀ {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ) {a b : ℕ} (SS : Finset (HeightOneSpectrum (𝓞 X.E))) (cl : ℕ) (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)) (Ξ : HomE X.E a b → ℂ), TaylorLogMetric.IsCurveIdeal D cc → TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ → δ ≠ 0 → B.VecP χ → 0 < cl → (∀ Q ∈ (SS.map (HeightOneSpectrum.equivOfRingEquiv (RingOfIntegers.mapRingEquiv s.iE)).toEmbedding), conjPrime₂ Q ∉ (SS.map (HeightOneSpectrum.equivOfRingEquiv (RingOfIntegers.mapRingEquiv s.iE)).toEmbedding)) → TaylorLogMetric.admitted D a b (s.lat N) (s.lat N') → DatLoc D cc (SS.map (HeightOneSpectrum.equivOfRingEquiv (RingOfIntegers.mapRingEquiv s.iE)).toEmbedding) cl (s.lat N) (s.lat N') (fun x => Ξ (seamHom s x)) → s.push (thC (X.embC s.σ₀) δ D.host.d (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ))⁻¹ (ambOf s B χ cD).AA SS N N' cl Ξ ((ambOf s B χ cD).e a b N N')) = kerTh B χ (SS.map (HeightOneSpectrum.equivOfRingEquiv (RingOfIntegers.mapRingEquiv s.iE)).toEmbedding) cl (s.lat N) (s.lat N') (fun x => Ξ (seamHom s x)) := by
  intro D X s hs cc δ B χ cD a b SS cl N N' Ξ hcc hδ hδ0 hVec hcl hSS hA hDat
  classical
  have hyp := KerMove.split_of_adm _ cl (s.lat N) (s.lat N') B hcc hδ hδ0 hA hcl hSS
  have hI := KerMove.finIdx_of_adm (cc := cc) (δ := δ) (SS.map (HeightOneSpectrum.equivOfRingEquiv (RingOfIntegers.mapRingEquiv s.iE)).toEmbedding) cl (s.lat N) (s.lat N') hA hcl
  have hθ := KerMove.eNat_fixed (s.lat N) (s.lat N') B χ hcc hδ hVec hA
  have := KerMove.tau_nonempty D
  have hΦ := hDat.invOn (fun τ => TaylorLogMetric.embT D τ) δ (embH_inj _ hδ0)
  have hper := GlobalTheory.T.hostHomToColumnFieldHom_mem_periodLattice_iff s hs B χ cD SS cl N N'
  have hemb := GlobalTheory.T.complexCoordinates_columnFieldIdentification s hs δ (a := a) (b := b)
  have hexp := GlobalTheory.T.primeSetExponent_transport_fieldIsomorphism s hs SS
  have hΛ := hemb.2.2.1 _ _ hper
  have hAh := hemb.2.2.1 _ _ (GlobalTheory.T.hostHomToColumnFieldHom_mem_twistedLattice_iff s _ _ hper cl (fun Q => -expS SS Q)
    (fun Q => -expS (SS.map (HeightOneSpectrum.equivOfRingEquiv (RingOfIntegers.mapRingEquiv s.iE)).toEmbedding) Q)
    (fun P => by simp only [hexp]))
  have hBh := hemb.2.2.1 _ _ (GlobalTheory.T.hostHomToColumnFieldHom_mem_twistedLattice_iff s _ _ hper cl (expS SS)
    (expS (SS.map (HeightOneSpectrum.equivOfRingEquiv (RingOfIntegers.mapRingEquiv s.iE)).toEmbedding)) hexp)
  have hdat : onV (fun τ => TaylorLogMetric.embT D τ) δ (fun x => Ξ (seamHom s x)) = fun v => onV (X.embC s.σ₀) δ Ξ (seamT s a b v) :=
    funext fun v => (hemb.2.2.2 hδ0 Ξ v).symm
  have hvec : B.eNat χ a b (s.lat N) (s.lat N') = fun v => (ambOf s B χ cD).e a b N N' (seamT s a b v) := by
    funext v
    show B.eNat χ a b (s.lat N) (s.lat N') v = B.eNat χ a b (s.lat N) (s.lat N') (fun τ => v (s.iT (s.iT.symm τ)))
    simp only [Equiv.apply_symm_apply]
  have hθ' : (fun v => (ambOf s B χ cD).e a b N N' (seamT s a b v)) ∈ fixedBy _ _ _ := hvec ▸ hθ
  have hΦ' : InvOn _ _ (fun v => onV (X.embC s.σ₀) δ Ξ (seamT s a b v)) := hdat ▸ hΦ
  funext z
  unfold Seam.push kerTh thC xiV
  rw [hdat, hvec]
  exact GlobalTheory.T.xiL_two_alt _ _ _ _ (seamT s a b) (HV_seamT s _) (alV_seamT s _ _) _ _ _ _ _ _ hyp hΛ hAh hBh
    ⟨_, repsOf_spec _ _ hI.1⟩ ⟨_, repsOf_spec _ _ hI.2.1⟩ ⟨_, repsOf_spec _ _ hI.2.2⟩ 1 _ _ hθ' hΦ' z

end GlobalTheory.TwU.SeamKer
end
end

section

open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.UG Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct

noncomputable section
namespace GlobalTheory.FrameRat

theorem nearAt_liftFr_smul : ∀ {D : D7} {X : Fields} (s : Seam D X) {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 X.E))} (d : DecoSet (E := X.E) (n := n) (ST := ST) (SG := SG)) (w : SG) (g : UF X.E n), ((qOf w.1 : ℕ) : 𝓞 X.E) ∉ w.1.asIdeal ^ 2 → ∀ (y : GL (Fin n) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)), NearAt (seamP s w.1) 1 y (seamGL s (d.1.liftFr w)) → NearAt (seamP s w.1) 1 (ratA D.host.F (seamGL s g.1) * y) (seamGL s (((g, (1 : GLG (E := X.E) (n := n) (SG := SG))) • d).1.liftFr w)) := by
  intro D X s n ST SG d w g hq y hy
  have hf := GlobalTheory.TopStep.liftFr_spec d.2 w
  have hf' : GlobalTheory.TopStep.IsLiftFr (d.1.act g.1 1) w (((g, (1 : GLG (E := X.E) (n := n) (SG := SG))) • d).1.liftFr w) := by
    have := GlobalTheory.TopStep.liftFr_spec ((g, (1 : GLG (E := X.E) (n := n) (SG := SG))) • d).2 w
    rwa [DecoSet.smul_val] at this
  set κ := GlobalTheory.TopStep.passFr g.1 1 hf hf' with hκ
  have hred : GlobalTheory.TopStep.redGL n w.1 κ = 1 := GlobalTheory.TopStep.redGL_passFr g.1 1 hf hf'
  have hred' : GlobalTheory.TopStep.redGL n w.1 κ⁻¹ = 1 := by rw [map_inv, hred, inv_one]
  have he : ((g, (1 : GLG (E := X.E) (n := n) (SG := SG))) • d).1.liftFr w = g.1 * d.1.liftFr w * (κ⁻¹).1 := by
    rw [InvMemClass.coe_inv, hκ]
    show _ = g.1 * d.1.liftFr w * ((((g, (1 : GLG (E := X.E) (n := n) (SG := SG))) • d).1.liftFr w)⁻¹ * g.1 * d.1.liftFr w)⁻¹
    group
  rw [he, map_mul, map_mul, mul_assoc, nearAt_rat_mul]
  exact GlobalTheory.CplPt.nearAt_mul 1 hy (GlobalTheory.CplPt.congAt_one_of_redGL s hq κ⁻¹ hred')

end GlobalTheory.FrameRat
end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix GlobalTheory.TwU GlobalTheory.TwU.AtTrue
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar



theorem GlobalTheory.TwU.AtTrue.charts_funKilled_one : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (i : ℕ) (hi : i ≤ B.R.m) (bad : Set (HeightOneSpectrum (𝓞 B.host.F))) (Ch : Type) (chOf : (I.stp u a i).Cl → Ch) (K0 : Fam I l Z u a i hi bad chOf), I.ReadsK l Z u a i hi chOf K0 → (∀ β, ∃ n : ℕ, 0 < n ∧ ∀ κ, (K0 β).lev.chi κ ^ n = 1) → ∃ Kc : Fam I l Z u a i hi bad chOf, ReadsOne I l Z u a i hi chOf Kc ∧ ∀ β, FunKilled (Kc β).lev (X.piT u) ∧ ∃ n : ℕ, 0 < n ∧ ∀ κ, (Kc β).lev.chi κ ^ n = 1 := by
  intro B X I hI hP l Z u a i hi bad Ch chOf K0 hK hfin
  obtain ⟨K', hK', hprop⟩ := TC.charts_funKilled I hI hP l Z u a i hi bad Ch chOf K0 hK
  obtain ⟨k, hk⟩ := GlobalTheory.T.chartsReadingStep_moveBasePoints_one_offLevelPrime I hI hP l Z u a i hi bad Ch chOf K' hK'
  refine ⟨fun β => moveChart (K' β) (k β), hk, fun β => ⟨(hprop β).1, ?_⟩⟩
  obtain ⟨hF, -, -, hU, hchi, -, -⟩ := hprop β
  obtain ⟨n, hn, hn'⟩ := hfin β
  refine ⟨n, hn, fun κ => ?_⟩
  have hm : (k β).1 * κ.1 * (k β).1⁻¹ ∈ (K0 β).lev.U := hU ▸ κ.2
  show ((K' β).lev.chi ⟨(k β).1 * κ.1 * (k β).1⁻¹, κ.2⟩) ^ n = 1
  have e := hchi ⟨(k β).1 * κ.1 * (k β).1⁻¹, κ.2⟩ ⟨_, hm⟩ rfl
  exact e.symm ▸ hn' _
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct
open GlobalTheory.TopStep

noncomputable section

namespace GlobalTheory.FramesDet

open Matrix
open scoped TensorProduct

section Cong

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {N : ℕ}
  {P : HeightOneSpectrum (𝓞 E)}

def intAtSub (P : HeightOneSpectrum (𝓞 E)) :
    Subring (E ⊗[F] FiniteAdeleRing (𝓞 F) F) where
  carrier := {a | IntAtA (F := F) P a}
  mul_mem' := GlobalTheory.CplPt.intAtA_mul
  one_mem' := by simpa using GlobalTheory.CplPt.intAtA_int (F := F) (P := P) 1
  add_mem' := GlobalTheory.CplPt.intAtA_add
  zero_mem' := by simpa using GlobalTheory.CplPt.intAtA_int (F := F) (P := P) 0
  neg_mem' := by
    intro a ha
    have := GlobalTheory.CplPt.intAtA_mul (GlobalTheory.CplPt.intAtA_int (F := F) (P := P) (-1)) ha
    simpa using this

theorem det_congAt {d : ℕ} (hd : 1 ≤ d) {k : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)} (h : CongAt P d k) :
    IntAtA (F := F) P (iA F E ((qOf P : ℕ) : E)⁻¹ *
      (((Matrix.GeneralLinearGroup.det k : (E ⊗[F] FiniteAdeleRing (𝓞 F) F)ˣ) : E ⊗[F] FiniteAdeleRing (𝓞 F) F) - 1)) := by
  classical
  set S := intAtSub (F := F) P with hS
  have hq : ((qOf P : ℕ) : E) ≠ 0 := by
    have : qOf P ≠ 0 := fun h0 => P.ne_bot (Ideal.absNorm_eq_zero_iff.1 h0)
    exact_mod_cast this
  set Q := iA F E ((qOf P : ℕ) : E) with hQ
  have hcQ : iA F E ((qOf P : ℕ) : E)⁻¹ * Q = 1 := by rw [hQ, ← map_mul, inv_mul_cancel₀ hq, map_one]
  have hQS : Q ∈ S := by
    have := GlobalTheory.CplPt.intAtA_int (F := F) (P := P) ((qOf P : ℕ) : 𝓞 E)
    simpa [hQ] using this
  have hZ : ∀ a b, Q ^ (d - 1) * (iA F E (((qOf P : ℕ) : E) ^ d)⁻¹ *
      ((k : Matrix (Fin N) (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) - 1) a b) ∈ S :=
    fun a b => S.mul_mem (S.pow_mem hQS _) (h a b)
  have hZe : ∀ a b, Q * (Q ^ (d - 1) * (iA F E (((qOf P : ℕ) : E) ^ d)⁻¹ *
      ((k : Matrix (Fin N) (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) - 1) a b)) =
      ((k : Matrix (Fin N) (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) - 1) a b := by
    intro a b
    have e : Q * Q ^ (d - 1) * iA F E (((qOf P : ℕ) : E) ^ d)⁻¹ = 1 := by
      rw [← pow_succ', Nat.sub_add_cancel hd, hQ, ← map_pow, ← map_mul, mul_inv_cancel₀ (pow_ne_zero _ hq), map_one]
    rw [← mul_assoc, ← mul_assoc, e, one_mul]
  let Z : Matrix (Fin N) (Fin N) S := fun a b => ⟨_, hZ a b⟩
  let q' : S := ⟨Q, hQS⟩
  let M : Matrix (Fin N) (Fin N) S := 1 + q' • Z
  have hM : M.map S.subtype = (k : Matrix (Fin N) (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) := by
    ext a b
    have e1 : S.subtype ((1 : Matrix (Fin N) (Fin N) S) a b) = (1 : Matrix (Fin N) (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) a b := by
      rw [Matrix.one_apply, Matrix.one_apply]; split_ifs <;> simp
    rw [Matrix.map_apply]
    simp only [M]
    rw [Matrix.add_apply, map_add (f := _), e1, Matrix.smul_apply, smul_eq_mul, map_mul]
    show _ + Q * (Q ^ (d - 1) * _) = _
    rw [hZe, Matrix.sub_apply]
    ring_nf
  set I : Ideal S := Ideal.span {q'}
  have hMI : M.map (Ideal.Quotient.mk I) = 1 := by
    ext a b
    have hq0 : Ideal.Quotient.mk I q' = 0 := Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span rfl)
    rw [Matrix.map_apply]
    simp only [M]
    rw [Matrix.add_apply, map_add (f := _), Matrix.smul_apply, smul_eq_mul, map_mul, hq0, zero_mul, add_zero,
      Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  have hdet : Ideal.Quotient.mk I M.det = Ideal.Quotient.mk I 1 := by
    rw [RingHom.map_det, map_one]
    show (M.map (Ideal.Quotient.mk I)).det = 1
    rw [hMI, Matrix.det_one]
  obtain ⟨w, hw⟩ := Ideal.mem_span_singleton'.1 (Ideal.Quotient.eq.1 hdet)
  have hk : ((Matrix.GeneralLinearGroup.det k : (E ⊗[F] FiniteAdeleRing (𝓞 F) F)ˣ) : E ⊗[F] FiniteAdeleRing (𝓞 F) F) =
      S.subtype M.det := by
    rw [RingHom.map_det, Matrix.GeneralLinearGroup.val_det_apply]
    exact congrArg Matrix.det hM.symm
  have e2 : iA F E ((qOf P : ℕ) : E)⁻¹ *
      (((Matrix.GeneralLinearGroup.det k : (E ⊗[F] FiniteAdeleRing (𝓞 F) F)ˣ) : E ⊗[F] FiniteAdeleRing (𝓞 F) F) - 1) = (w : _) := by
    rw [hk, show S.subtype M.det - 1 = S.subtype (M.det - 1) by simp, ← hw, map_mul]
    show iA F E ((qOf P : ℕ) : E)⁻¹ * ((w : _) * Q) = _
    rw [mul_comm (w : E ⊗[F] FiniteAdeleRing (𝓞 F) F), ← mul_assoc, hcQ, one_mul]
  rw [e2]
  exact w.2

end Cong

section Rat

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

theorem det_ratA (g : GL (Fin n) E) :
    ((Matrix.GeneralLinearGroup.det (ratA F g) : (E ⊗[F] FiniteAdeleRing (𝓞 F) F)ˣ) : E ⊗[F] FiniteAdeleRing (𝓞 F) F) =
      iA F E ((Matrix.GeneralLinearGroup.det g : Eˣ) : E) := by
  rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.GeneralLinearGroup.val_det_apply, RingHom.map_det]
  rfl

end Rat

section Frame

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {X : Fields} (s : Seam D X)

theorem det_seamGL {n : ℕ} (g : Sp X.E n ≃ₗ[X.E] Sp X.E n) :
    ((Matrix.GeneralLinearGroup.det (seamGL s g) : D.host.Eˣ) : D.host.E) = s.iE ((LinearEquiv.det g : X.Eˣ) : X.E) := by
  have h : ((seamGL s g : GL (Fin n) D.host.E) : Matrix (Fin n) (Fin n) D.host.E) =
      (LinearMap.toMatrix' g.toLinearMap).map (s.iE : X.E →+* D.host.E) := rfl
  rw [Matrix.GeneralLinearGroup.val_det_apply, h, ← RingHom.mapMatrix_apply, ← RingHom.map_det, LinearMap.det_toMatrix',
    LinearEquiv.coe_det]
  rfl

variable {i : ℕ} {SB : Finset (HeightOneSpectrum (𝓞 X.E))} (fb : SB → GL (Fin (D.R.N i)) D.host.E) (dep : SB → ℕ)

theorem det_inFrame {P : SB} {κ : GL (Fin (D.R.N i)) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)}
    {g : Sp X.E (D.R.N i) ≃ₗ[X.E] Sp X.E (D.R.N i)} (hd : 1 ≤ dep P) (h : InFrame s fb dep P κ g) :
    IntAtA (F := D.host.F) (seamP s P.1) (iA D.host.F D.host.E ((qOf (seamP s P.1) : D.host.E))⁻¹ *
      ((((Matrix.GeneralLinearGroup.det κ)⁻¹ : (AfE D.host.F D.host.E)ˣ) : AfE D.host.F D.host.E) *
        iA D.host.F D.host.E (s.iE ((LinearEquiv.det g : X.Eˣ) : X.E)) - 1)) := by
  have H := det_congAt hd h
  have e : ((Matrix.GeneralLinearGroup.det (((ratA D.host.F (fb P))⁻¹ * κ * ratA D.host.F (fb P))⁻¹ *
      ratA D.host.F (seamGL s g)) : (AfE D.host.F D.host.E)ˣ) : AfE D.host.F D.host.E) =
      (((Matrix.GeneralLinearGroup.det κ)⁻¹ : (AfE D.host.F D.host.E)ˣ) : AfE D.host.F D.host.E) *
        iA D.host.F D.host.E (s.iE ((LinearEquiv.det g : X.Eˣ) : X.E)) := by
    rw [map_mul, map_inv, map_mul, map_mul, map_inv, Units.val_mul, det_ratA, det_seamGL]
    congr 2
    rw [mul_comm, mul_inv_cancel_left]
  rw [← e]
  exact H

theorem det_inFrame_mul {P : SB} (hd : 1 ≤ dep P)
    (κ : GL (Fin (D.R.N i)) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F))
    (g C : Sp X.E (D.R.N i) ≃ₗ[X.E] Sp X.E (D.R.N i)) (h : InFrame s fb dep P κ g)
    (hC : CongAt (F := D.host.F) (seamP s P.1) (dep P) (ratA D.host.F (seamGL s C))) :
    IntAtA (F := D.host.F) (seamP s P.1) (iA D.host.F D.host.E ((qOf (seamP s P.1) : D.host.E))⁻¹ *
      ((((Matrix.GeneralLinearGroup.det κ)⁻¹ : (AfE D.host.F D.host.E)ˣ) : AfE D.host.F D.host.E) *
        iA D.host.F D.host.E (s.iE ((LinearEquiv.det (g * C) : X.Eˣ) : X.E)) - 1)) := by
  have hα := det_inFrame s fb dep hd h
  have hβ := det_congAt hd hC
  rw [det_ratA, det_seamGL] at hβ
  set U := (((Matrix.GeneralLinearGroup.det κ)⁻¹ : (AfE D.host.F D.host.E)ˣ) : AfE D.host.F D.host.E)
  set G := iA D.host.F D.host.E (s.iE ((LinearEquiv.det g : X.Eˣ) : X.E))
  set W := iA D.host.F D.host.E (s.iE ((LinearEquiv.det C : X.Eˣ) : X.E))
  set qi := iA D.host.F D.host.E ((qOf (seamP s P.1) : D.host.E))⁻¹
  set Q := iA D.host.F D.host.E ((qOf (seamP s P.1) : D.host.E))
  have hq : ((qOf (seamP s P.1) : ℕ) : D.host.E) ≠ 0 := by
    have : qOf (seamP s P.1) ≠ 0 := fun h0 => (seamP s P.1).ne_bot (Ideal.absNorm_eq_zero_iff.1 h0)
    exact_mod_cast this
  have hcQ : qi * Q = 1 := by
    simp only [qi, Q]; rw [← map_mul, inv_mul_cancel₀ hq, map_one]
  have hQ : IntAtA (F := D.host.F) (seamP s P.1) Q := by
    have := GlobalTheory.CplPt.intAtA_int (F := D.host.F) (P := seamP s P.1) ((qOf (seamP s P.1) : ℕ) : 𝓞 D.host.E)
    simpa [Q] using this
  have hdet : iA D.host.F D.host.E (s.iE ((LinearEquiv.det (g * C) : X.Eˣ) : X.E)) = G * W := by
    simp only [G, W]; rw [map_mul, Units.val_mul, map_mul, map_mul]
  have hW : W = Q * (qi * (W - 1)) + 1 := by
    linear_combination (1 - W) * hcQ
  have hWi : IntAtA (F := D.host.F) (seamP s P.1) W := by
    rw [hW]
    exact GlobalTheory.CplPt.intAtA_add (GlobalTheory.CplPt.intAtA_mul hQ hβ) (by simpa using GlobalTheory.CplPt.intAtA_int (F := D.host.F) (P := seamP s P.1) 1)
  have e : qi * (U * (G * W) - 1) = qi * (U * G - 1) * W + qi * (W - 1) := by ring
  rw [hdet, e]
  exact GlobalTheory.CplPt.intAtA_add (GlobalTheory.CplPt.intAtA_mul hα hWi) hβ

end Frame

end GlobalTheory.FramesDet

theorem GlobalTheory.FramesDet.det_frame_mul_congAt : ∀ {D : D7} {X : Fields} (s : Seam D X) {i : ℕ} {SB : Finset (HeightOneSpectrum (𝓞 X.E))}
    (fb : SB → GL (Fin (D.R.N i)) D.host.E) (dep : SB → ℕ) (P : SB), 1 ≤ dep P →
    ∀ (κ : GL (Fin (D.R.N i)) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F))
      (g C : Sp X.E (D.R.N i) ≃ₗ[X.E] Sp X.E (D.R.N i)), InFrame s fb dep P κ g →
    CongAt (F := D.host.F) (seamP s P.1) (dep P) (ratA D.host.F (seamGL s C)) →
    IntAtA (F := D.host.F) (seamP s P.1) (iA D.host.F D.host.E ((qOf (seamP s P.1) : D.host.E))⁻¹ *
      ((((Matrix.GeneralLinearGroup.det κ)⁻¹ : (AfE D.host.F D.host.E)ˣ) : AfE D.host.F D.host.E) *
        iA D.host.F D.host.E (s.iE ((LinearEquiv.det (g * C) : X.Eˣ) : X.E)) - 1)) := by
  intro D X s i SB fb dep P hd κ g C h hC
  exact GlobalTheory.FramesDet.det_inFrame_mul s fb dep hd κ g C h hC
end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField


theorem _root_.GlobalTheory.T.algebraicModularForms_heckeModules_iso_all_places : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (a : NG.AlgWt L n) (S₁ S₂ : Submodule ℂ (GAf L n → a.W)), NG.IsIrrRep a.ρ S₁ → NG.IsIrrRep a.ρ S₂ → (∀ s : SplitPlace L, ∃ σ₁ σ₂ : GlobalTheory.SmGL.IrrRep (GL (Fin n) (s.w.adicCompletion L)), IsLocS S₁ s σ₁ ∧ IsLocS S₂ s σ₂ ∧ Nonempty (σ₁.ρ.Equiv σ₂.ρ)) → (∀ v : HeightOneSpectrum (𝓞 (maximalRealSubfield L)), (∀ s : SplitPlace L, s.v ≠ v) → ∃ (w : HeightOneSpectrum (𝓞 L)) (Dv : InertDatum L n v w) (α : Fin (n / 2) → ℂ), NG.OverPl w v ∧ (∃ f ∈ S₁, f ≠ 0 ∧ ∀ κ ∈ Umax L n, TrivOutside {v} κ → NG.rt L n κ f = f) ∧ (∃ f ∈ S₂, f ≠ 0 ∧ ∀ κ ∈ Umax L n, TrivOutside {v} κ → NG.rt L n κ f = f) ∧ ∀ U : Subgroup (GAf L n), (∀ κ, TrivOutside {v} κ → (κ ∈ U ↔ κ ∈ Umax L n)) → ∀ h ∈ Formalism.UG.Hecke ℂ (Formalism.UG.KU Dv.σw n), (∀ f ∈ S₁, (∀ κ ∈ U, NG.rt L n κ f = f) → heckeFunI L n U Dv h f = Formalism.UG.SatU Dv.ϖ (Formalism.UG.qV (maximalRealSubfield L) v) h α • f) ∧ (∀ f ∈ S₂, (∀ κ ∈ U, NG.rt L n κ f = f) → heckeFunI L n U Dv h f = Formalism.UG.SatU Dv.ϖ (Formalism.UG.qV (maximalRealSubfield L) v) h α • f)) → ∀ N : ℕ, 0 < N → (∃ f ∈ S₁, (∀ κ, NG.Cong L n N κ → NG.rt L n κ f = f) ∧ f ≠ 0) → ∃ φ : (GAf L n → a.W) →ₗ[ℂ] (GAf L n → a.W), (∀ f ∈ S₁, (∀ κ, NG.Cong L n N κ → NG.rt L n κ f = f) → φ f ∈ S₂ ∧ ∀ κ, NG.Cong L n N κ → NG.rt L n κ (φ f) = φ f) ∧ (∃ f ∈ S₁, (∀ κ, NG.Cong L n N κ → NG.rt L n κ f = f) ∧ φ f ≠ 0) ∧ (∀ (g : GAf L n) (f : GAf L n → a.W), f ∈ S₁ → (∀ κ, NG.Cong L n N κ → NG.rt L n κ f = f) → φ (NG.heckeD (GlobalTheory.IsotOrth.congSub L n N) {x | ∃ u ∈ GlobalTheory.IsotOrth.congSub L n N, ∃ u' ∈ GlobalTheory.IsotOrth.congSub L n N, x = u * g * u'} f) = NG.heckeD (GlobalTheory.IsotOrth.congSub L n N) {x | ∃ u ∈ GlobalTheory.IsotOrth.congSub L n N, ∃ u' ∈ GlobalTheory.IsotOrth.congSub L n N, x = u * g * u'} (φ f)) := by
  first | exact @GlobalTheory.HeckeIso.main | exact GlobalTheory.HeckeIso.main | (intros; apply GlobalTheory.HeckeIso.main <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil

theorem _root_.GlobalTheory.T.spherical_twist_of_blockTypeVector : GlobalTheory.Published.BernsteinZelevinskyFiniteness → GlobalTheory.Published.GeometricLemma → GlobalTheory.Published.DepthZeroJacquetInjective → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (r t : ℕ) (χ : kˣ →* ℂˣ) (π : Irr k (r + t)) (π₁ : Irr k r) (π₂ : Irr k t) (v : π.V), IsSmoothChar χ → IsTame χ → (∀ α : ℂˣ, ¬ InSupport π₁.π (χ * unrChar k α)) → Nonempty (π.π.Equiv (prod₂ π₁.π π₂.π)) → v ≠ 0 → IsBlockVec χ π.π v → IsSpherical (_root_.GlobalTheory.SmGL.twist π₂.π (detChar (Fin t) χ⁻¹)) := by
  first | exact @GlobalTheory.BlockSph.sph_of_isBlockVec | exact GlobalTheory.BlockSph.sph_of_isBlockVec | (intros; apply GlobalTheory.BlockSph.sph_of_isBlockVec <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil


theorem _root_.GlobalTheory.T.isSubquotient_prod_reordered_cuspSupport : GlobalTheory.Published.BernsteinZelevinskyFiniteness → GlobalTheory.Published.GeometricLemma → GlobalTheory.Published.UnlinkedProductIrreducible → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (r t s : ℕ) (π : Irr k (r + t)) (d : Fin s → ℕ) (σ : ∀ a, Irr k (d a)) (S : Finset (Fin s)), IsCuspSupport π.π d (fun a => (σ a).π) → (∀ b ∈ S, d b = 1) → (∀ a b, a ∉ S → b ∈ S → ∀ (h : d a = d b) (α : ℂˣ), ¬ Nonempty ((h ▸ σ a : Irr k (d b)).π.Equiv (_root_.GlobalTheory.SmGL.twist (σ b).π (detChar (Fin (d b)) (unrChar k α))))) → ∑ a ∈ Sᶜ, d a = r → ∑ a ∈ S, d a = t → ∃ (s₁ s₂ : ℕ) (ι₁ : Fin s₁ → Fin s) (ι₂ : Fin s₂ → Fin s) (e₁ : (Σ a, Fin (d (ι₁ a))) ≃ Fin r) (e₂ : (Σ b, Fin (d (ι₂ b))) ≃ Fin t) (V₁ V₂ : Type) (_ : AddCommGroup V₁) (_ : Module ℂ V₁) (_ : AddCommGroup V₂) (_ : Module ℂ V₂) (ρ₁ : Representation ℂ (GL (Fin r) k) V₁) (ρ₂ : Representation ℂ (GL (Fin t) k) V₂), (∀ a, ι₁ a ∉ S) ∧ (∀ b, ι₂ b ∈ S) ∧ IsSmooth ρ₁ ∧ IsSmooth ρ₂ ∧ Nonempty (ρ₁.Equiv (multiProd e₁ fun a => (σ (ι₁ a)).π)) ∧ Nonempty (ρ₂.Equiv (multiProd e₂ fun b => (σ (ι₂ b)).π)) ∧ IsSubquotient π.π (prod₂ ρ₁ ρ₂) := by
  first | exact @GlobalTheory.isSubquotient_prod₂_of_cuspSupport_reorder | exact GlobalTheory.isSubquotient_prod₂_of_cuspSupport_reorder | (intros; apply GlobalTheory.isSubquotient_prod₂_of_cuspSupport_reorder <;> assumption)
end
