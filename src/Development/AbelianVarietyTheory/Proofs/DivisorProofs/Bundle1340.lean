module

public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallyExistsFiniteSubsetNonzeroLocus
public import Development.AbelianVarietyTheory.Definitions.Divisors.LineBundleGlobalSectionsDimCongrPicardClass
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallySubsingletonCohTwistZOfIsProjOver
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsFiniteLengthOfIsArtinianRingAnnihilator
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1227
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1139
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RestrictPullbackIsoHomAppPullbackSections
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1241
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle014
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle015
public import Development.AbelianVarietyTheory.Definitions.Divisors.SimpleTwistedTraceFormulaStable
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle049
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1249
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle104
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1248
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1230
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Algebra.Ring.IsFormallyReal
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle038
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsAlgHomOfIsBaseChange
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsQuasicoherentOfForallExistsAffine
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.IsQuasicoherentOfLocallyIso
import Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle004
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle036
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction

@[expose] public section

section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

namespace GlobalTheory.PairStep

theorem exists_sec_mem_not_mem_of_not_specializes :
    ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (N : LB X) (x z : X), IsAmpleLB N → ¬ z ⤳ x →
      ∃ (l : ℕ) (s : (lbPow N l).Sec), 0 < l ∧ x ∈ nonzeroLocus s ∧ z ∉ nonzeroLocus s := by
  intro X _ _ N x z hN hzx
  let U : X.Opens := ⟨(closure ({z} : Set X))ᶜ, isClosed_closure.isOpen_compl⟩
  have hx : x ∈ U := fun h => hzx (specializes_iff_mem_closure.2 h)
  obtain ⟨n, hn, s, hs, hle, -⟩ := hN.exists_affine_le hx
  exact ⟨n, s, hn, hs, fun h => hle h (subset_closure rfl)⟩

end GlobalTheory.PairStep
end

section

set_option autoImplicit false

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter Asymptotics
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist

namespace GlobalTheory

theorem hdim_twist_zero_le_of_cls_eq_add_nsmul (k : Type) [Field k] [Infinite k] (X : Scheme.{0})
    [Algebra k Γ(X, ⊤)] (hX : IsProjOver (strHom k (X := X))) (F : X.Modules) [IsFiniteQC F]
    (B : LB X) (hB : B.IsLB) (s : B.Sec) (hs : Mono (cutHom F hB s)) (j : ℕ) :
    ∀ (M M' : LB X) (hM : M.IsLB) (hM' : M'.IsLB), cls M hM = cls M' hM' + j • cls B hB →
      hdim k (twist F M') 0 ≤ hdim k (twist F M) 0 := by
  induction j with
  | zero =>
    intro M M' hM hM' e
    obtain ⟨e⟩ := nonempty_twist_iso_of_cls_eq F hM hM' (by simpa using e)
    exact (hdim_congr k 0 e).ge
  | succ j ih =>
    intro M M' hM hM' e
    obtain ⟨N, hN, eN⟩ := cls_surj (cls M' hM' + j • cls B hB)
    exact (ih N M' hN hM' eN).trans
      (GlobalTheory.T.sheafCohomologyDim_twist_cut_inequalities k X hX F B M N hB hM hN s hs (by rw [e, eN, succ_nsmul, add_assoc])).2.2

theorem exists_hdim_twist_lbPow_zero_le :
    ∀ (k : Type) [Field k] [Infinite k] (X : Scheme.{0}) [Algebra k Γ(X, ⊤)], IsProjOver (strHom k (X := X)) → ∀ (d : ℕ) (L : LB X), L.IsLB → ∀ (F : X.Modules) [IsFiniteQC F], suppDim F ≤ (d : ℕ) → ∃ C : ℕ, ∀ m : ℕ, hdim k (twist F (lbPow L m)) 0 ≤ C * (m + 1) ^ d := by
  intro k _ _ X _ hX d L hL F _ hF
  have := isNoetherian_of_isProjOver hX
  obtain ⟨-, A, hA⟩ := isProper_and_exists_isAmpleLB_of_isProjOver hX
  obtain ⟨D, hD, eD⟩ := cls_surj (-cls L hL)
  obtain ⟨n, hn, hn1⟩ := ((tendsto_natCast_atTop_atTop (R := ℤ).eventually
    (hA.eventually_exists_mono_cutHom hD F)).and (eventually_ge_atTop 1)).exists
  obtain ⟨B, hB, eB⟩ := cls_surj (cls D hD + (n : ℤ) • cls A hA.isLB)
  obtain ⟨s, hs⟩ := hn B hB eB
  have hH : IsAmpleLB (lbPow A n) := (isAmpleLB_pow_iff hA.isLB hn1).2 hA
  have h₁ : ∀ m : ℕ, hdim k (twist F (lbPow L m)) 0 ≤ hdim k (twist F (lbPow (lbPow A n) m)) 0 :=
    fun m => hdim_twist_zero_le_of_cls_eq_add_nsmul k X hX F B hB s hs m _ _
      (isLB_lbPow hH.isLB m) (isLB_lbPow hL m) (by
        rw [cls_lbPow hH.isLB, cls_lbPow hA.isLB, cls_lbPow hL, eB, eD, natCast_zsmul, ← nsmul_add,
          add_neg_cancel_left])
  obtain ⟨C, m₀, hC⟩ := GlobalTheory.T.asymptotic_riemannRoch_ample_coherent k X hX d F hF _ hH
  set a := interNum k F (fun _ : Fin d => lbPow A n)
  set h : ℕ → ℕ := fun m => hdim k (twist F (lbPow (lbPow A n) m)) 0 with hh
  refine ⟨a.natAbs + C * d + ∑ i ∈ Finset.range m₀, h i, fun m => (h₁ m).trans ?_⟩
  change h m ≤ _
  have hp : 1 ≤ (m + 1) ^ d := Nat.one_le_pow _ _ (Nat.succ_pos m)
  rcases lt_or_ge m m₀ with hm | hm
  · have : h m ≤ ∑ i ∈ Finset.range m₀, h i :=
      Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_range.2 hm)
    exact (this.trans (Nat.le_add_left _ _)).trans (Nat.le_mul_of_pos_right _ hp)
  · have h₂ : (d.factorial : ℤ) * (h m : ℤ) - a * (m : ℤ) ^ d ≤
        C * ((d : ℤ) * ((m : ℤ) + 1) ^ (d - 1)) := (abs_le.1 (hC m hm)).2
    have h₃ : (h m : ℤ) ≤ (d.factorial : ℤ) * (h m : ℤ) :=
      le_mul_of_one_le_left (by positivity) (by exact_mod_cast d.factorial_pos)
    have h₄ : a * (m : ℤ) ^ d ≤ |a| * ((m : ℤ) + 1) ^ d :=
      (mul_le_mul_of_nonneg_right (le_abs_self a) (by positivity)).trans
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) (by linarith) d) (abs_nonneg a))
    have h₅ : (C : ℤ) * ((d : ℤ) * ((m : ℤ) + 1) ^ (d - 1)) ≤ C * ((d : ℤ) * ((m : ℤ) + 1) ^ d) := by
      gcongr
      · have : (0 : ℤ) ≤ m := by positivity
        linarith
      · exact Nat.sub_le _ _
    have h₆ : (h m : ℤ) ≤ ((a.natAbs + C * d) * (m + 1) ^ d : ℕ) := by
      push_cast
      linarith
    exact (by exact_mod_cast h₆ : h m ≤ _).trans (Nat.mul_le_mul_right _ (Nat.le_add_right _ _))

end GlobalTheory
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Points GlobalTheory.CxPts GlobalTheory.VB
open GlobalTheory.QCoh (pullbackSections res_pullbackSections)
open GlobalTheory.Twist (resM app_resM)

namespace GlobalTheory.PullPull

section Sections

variable {X Y Z : Scheme.{0}}

theorem pullbackComp_hom_app (b : Z ⟶ Y) (a : Y ⟶ X) (E : X.Modules) {U : X.Opens} {V : Y.Opens}
    {T : Z.Opens} (h₁ : V ≤ a ⁻¹ᵁ U) (h₂ : T ≤ b ⁻¹ᵁ V) (h : T ≤ (b ≫ a) ⁻¹ᵁ U) (s : Γ(E, U)) :
    ((Scheme.Modules.pullbackComp b a).hom.app E).app T
        (pullbackSections b _ h₂ (pullbackSections a E h₁ s)) =
      pullbackSections (b ≫ a) E h s := by
  rw [← Vert.DivPull.pullbackComp_inv_app b a E h₁ h₂ h s]
  have e : (Scheme.Modules.pullbackComp b a).inv.app E ≫
      (Scheme.Modules.pullbackComp b a).hom.app E = 𝟙 _ := by simp
  exact congr(($e).app T (pullbackSections (b ≫ a) E h s))

end Sections

section Met

variable {k : Type} [CommRing k] {X Y Z : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ}
  {E E' : X.Modules} {r : ℕ}

end Met

end GlobalTheory.PullPull

namespace GlobalTheory.VMetric

end GlobalTheory.VMetric
end
end

section

open NumberField CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.ChowHt GlobalTheory.CompHt
open scoped Classical
attribute [local instance] MvPolynomial.gradedAlgebra

namespace GlobalTheory.HermLB

theorem isometric_pull_fs_toProj : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (L : GlobalTheory.HermLB p) (m : ℕ) (t : Fin (m + 1) → L.B.Sec) (ht : ⨆ j, nonzeroLocus (t j) = ⊤)
    (A : (k →+* ℂ) → Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) (hA : ∀ σ, (A σ).det ≠ 0)
    (hc : ∀ σ, ∃ U ∈ Matrix.unitaryGroup (Fin (m + 1)) ℂ, A ((starRingEnd ℂ).comp σ) = (A σ).map (starRingEnd ℂ) * U),
    (∀ (σ : k →+* ℂ) (i : L.B.ι) (y : GlobalTheory.CxPts p σ), y ∈ ptsIn p σ (L.B.U i) →
      (L.φ σ).φ i y = Real.log (∑ a, ‖∑ j, A σ j a * valR y.1 (L.B.U i) ((t j).f i)‖ ^ 2)) →
    ((GlobalTheory.HermLB.fs (PSpace.str k m) (GlobalTheory.ProjSpace.O1_isLB k m) (GlobalTheory.ProjSpace.coord k m) (GlobalTheory.ProjSpace.iSup_nonzeroLocus_coord k m) A hA hc).pull
      (GlobalTheory.ProjSpace.toProj p t ht) (GlobalTheory.ProjSpace.toProj_str p t ht)).Isometric L := by
  intro k _ X p L m t ht A hA hc h
  refine ⟨ProjSpace.toProjIso p t ht, ProjSpace.toProjIso_isGen p t ht, fun σ a b y ha hb => ?_⟩
  let π := ProjSpace.toProj p t ht
  have hπ : π ≫ PSpace.str k m = p := ProjSpace.toProj_str p t ht
  let z := Points.PtsOver.map π hπ (spMap σ) y
  let B := (ProjSpace.O1 k m).pull π
  have hb' : y ∈ ptsIn p σ (B.U b) := hb
  have hab : y ∈ ptsIn p σ (L.B.U a ⊓ B.U b) := mem_ptsIn_inf.2 ⟨ha, hb'⟩
  have hz : z ∈ ptsIn (PSpace.str k m) σ ((ProjSpace.O1 k m).U (b PUnit.unit)) :=
    mem_of_mem_linComb (m := fun _ => z) (fun _ => rfl) hb' PUnit.unit
  let u : Γ(X, L.B.U a ⊓ B.U b)ˣ := (ProjSpace.toProjIso p t ht).s (a, b)
  let r : Fin (m + 1) → ℂ := fun j =>
    valR z.1 ((ProjSpace.O1 k m).U (b PUnit.unit)) ((ProjSpace.coord k m j).f (b PUnit.unit))
  have hu : ev p σ _ u.val y ≠ 0 := ev_ne_zero hab u.isUnit
  have e (j) : valR y.1 (L.B.U a) ((t j).f a) = ev p σ _ u.val y * r j := by
    have e₁ : resG X (inf_le_left : L.B.U a ⊓ B.U b ≤ L.B.U a) ((t j).f a) =
        u.val * resG X inf_le_right ((Cartier.secPull (ProjSpace.coord k m j) π).f b) :=
      ProjSpace.secMaps_toProjIso p t ht j (a, b)
    have e₂ := congrArg (ev p σ _ · y) e₁
    simp only [ev_mul, ev_res _ hab] at e₂
    exact e₂.trans (congrArg (_ * ·) (Points.valR_appLE y.1 π _ hb' _))
  have h0 := (Weight.noCommonZero_combVal (p := PSpace.str k m) (σ := σ)
    (ProjSpace.iSup_nonzeroLocus_coord k m) (hA σ)).sum_pos hz
  have h0' : 0 < ∑ c, ‖∑ j, A σ j c * r j‖ ^ 2 := h0.trans_eq (Finset.sum_congr rfl fun c _ =>
    congrArg (‖·‖ ^ 2) ((congrFun (Finset.sum_apply _ _ _) z).trans (Finset.sum_apply _ _ _)))
  have e₃ := (Weight.pull_φ (Weight.fsBasis (PSpace.str k m) σ (ProjSpace.O1_isLB k m) (ProjSpace.coord k m)
    (ProjSpace.iSup_nonzeroLocus_coord k m) (A σ) (hA σ)) π hπ b y).trans (Weight.fsBasis_φ _ _ _ _ _ _ _)
  refine (h σ a y ha).trans (Eq.trans ?_ (congrArg (· + Real.log (‖ev p σ _ u.val y‖ ^ 2)) e₃.symm))
  refine Eq.trans ?_ (Real.log_mul h0'.ne' (pow_ne_zero 2 (norm_ne_zero_iff.2 hu)))
  rw [Finset.sum_mul]
  refine congrArg _ (Finset.sum_congr rfl fun c _ => ?_)
  rw [← mul_pow, ← norm_mul, Finset.sum_mul]
  refine congrArg (‖·‖ ^ 2) (Finset.sum_congr rfl fun j _ => ?_)
  rw [e j]
  ring

end GlobalTheory.HermLB
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.exists_compact_invertible_krylovMatrices : ∀ (E : Type) [Field E] [NumberField E] (w : Pl E) (r : ℕ) (Ω : Set (GLw r w)), IsCompact Ω → (∀ y ∈ Ω, ∃ e, IsUnit (GlobalTheory.LeviDesc.Krylov.krylov y.val e).det) → ∃ C : Set (GLw r w), IsCompact C ∧ ∀ y ∈ Ω, ∃ e, ∃ c ∈ C, c.val = GlobalTheory.LeviDesc.Krylov.krylov y.val e := by
  first | exact @GlobalTheory.LeviDesc.Krylov.exists_isCompact_krylov_units | exact GlobalTheory.LeviDesc.Krylov.exists_isCompact_krylov_units | (intros; apply GlobalTheory.LeviDesc.Krylov.exists_isCompact_krylov_units <;> assumption)
end

section

open MeasureTheory GlobalTheory.JSW
open scoped FourierTransform ContDiff

theorem _root_.GlobalTheory.T.unipotentLowerRowsLeviSet_closed_subgroup : ∀ (n r : ℕ), (∀ g ∈ levSet n r, ∀ h ∈ levSet n r, g * h ∈ levSet n r) ∧ (∀ g ∈ levSet n r, g⁻¹ ∈ levSet n r) ∧ (∀ u ∈ GlobalTheory.SmGL.unipB ℂ (Fin n), u ∈ levSet n r) ∧ IsClosed (levSet n r) := by
  first | exact @GlobalTheory.JSW.levSet_closed_subgroup | exact GlobalTheory.JSW.levSet_closed_subgroup | (intros; apply GlobalTheory.JSW.levSet_closed_subgroup <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField MeasureTheory
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix Formalism.IndefR.Datum
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
open scoped Pointwise
namespace GlobalTheory.ThetaParsevalInner

theorem setIntegral_eq_zero_of_twist {V : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]
    [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddLeftInvariant] (G : AddSubgroup V) [Countable G]
    {s : Set V} (hs : IsAddFundamentalDomain G s μ) {h : V → ℂ} (hper : ∀ g ∈ G, ∀ y, h (g + y) = h y)
    {c : V} {a : ℂ} (hc : ∀ y, h (c + y) = a * h y) (ha : a ≠ 1) : ∫ y in s, h y ∂μ = 0 := by
  have ht : IsAddFundamentalDomain G (c +ᵥ s) μ := hs.vadd_of_comm c
  have e1 : ∫ y in s, h y ∂μ = ∫ y in c +ᵥ s, h y ∂μ := hs.setIntegral_eq ht (fun g y => hper g g.2 y)
  have e2 : ∫ y in c +ᵥ s, h y ∂μ = ∫ y in s, h (c + y) ∂μ := by
    have := (measurePreserving_add_left μ c).setIntegral_preimage_emb (measurableEmbedding_addLeft c) h (c +ᵥ s)
    rw [← this]
    congr 2
    ext y
    simp [Set.mem_vadd_set_iff_neg_vadd_mem]
  have e3 : ∫ y in s, h (c + y) ∂μ = a * ∫ y in s, h y ∂μ := by
    simp_rw [hc]
    exact integral_const_mul a _
  have : (1 - a) * ∫ y in s, h y ∂μ = 0 := by rw [sub_mul, one_mul, ← e3, ← e2, ← e1, sub_self]
  exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr (Ne.symm ha))

theorem countable_numberField (F : Type) [Field F] [NumberField F] : Countable F :=
  Countable.of_equiv _ (Module.finBasis ℚ F).equivFun.toEquiv.symm

theorem lintegral_thetaSum_schr_sq : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsCharAF F ψ → ∀ (κ : Type) [Fintype κ]
    (μ : @Measure (κ → AF F) (borel _)), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
    ∀ (𝓕₁ : Set (κ → AF F)), @IsAddFundamentalDomain (GlobalTheory.ThetaParseval.ratVec F κ) _ _ _ (borel _) 𝓕₁ μ →
      μ 𝓕₁ ≠ ⊤ → ∀ Φ ∈ GlobalTheory.WeilM.schA F κ, ∀ x : (κ → AF F),
      ∫⁻ y in 𝓕₁, ‖GlobalTheory.WeilM.thetaSum F (GlobalTheory.WeilM.schr ψ (x, y) Φ)‖ₑ ^ 2 ∂μ =
        μ 𝓕₁ * ∑' ξ : κ → F, ‖Φ ((fun i => algebraMap F (AF F) (ξ i)) + x)‖ₑ ^ 2 := by
  intro F _ _ ψ hψ κ _ μ hμ 𝓕₁ hF hfin Φ hΦ x
  classical
  letI : MeasurableSpace (κ → AF F) := borel _
  haveI : BorelSpace (κ → AF F) := ⟨rfl⟩
  haveI : Countable F := countable_numberField F
  haveI : IsFiniteMeasure (μ.restrict 𝓕₁) := isFiniteMeasure_restrict.mpr hfin
  haveI := hμ
  obtain ⟨hcont, hnorm, htriv, s0, hs0⟩ := hψ
  obtain ⟨emb, hemb⟩ : ∃ emb : (κ → F) → (κ → AF F), emb = fun ξ i => algebraMap F (AF F) (ξ i) := ⟨_, rfl⟩
  obtain ⟨a, ha⟩ : ∃ a : (κ → F) → ℂ, a = fun ξ => Φ (emb ξ + x) := ⟨_, rfl⟩
  obtain ⟨e, he⟩ : ∃ e : (κ → F) → (κ → AF F) → ℂ, e = fun ξ y => ψ (emb ξ ⬝ᵥ y) := ⟨_, rfl⟩
  obtain ⟨g, hg⟩ : ∃ g : (κ → AF F) → ℂ, g = fun y => ∑' ξ, a ξ * e ξ y := ⟨_, rfl⟩
  have hsum : Summable fun ξ => ‖a ξ‖ := by
    have h0 := GlobalTheory.WeilM.summable_norm_of_mem_schA F (GlobalTheory.SchwartzTranslate.schA_translate F x hΦ)
    subst ha hemb
    exact h0
  have he_norm : ∀ ξ y, ‖e ξ y‖ = 1 := fun ξ y => by rw [he]; exact hnorm _
  have he_cont : ∀ ξ, Continuous (e ξ) := fun ξ => by
    rw [he]; exact hcont.comp (continuous_const.dotProduct continuous_id)
  have hconj : ∀ t, (starRingEnd ℂ) (ψ t) = ψ (-t) := fun t => by
    have h1 : ψ t * (starRingEnd ℂ) (ψ t) = 1 := by rw [Complex.mul_conj', hnorm]; simp
    have h2 : ψ t * ψ (-t) = 1 := by rw [← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one]
    have h0 : ψ t ≠ 0 := fun h => by simpa [h] using hnorm t
    exact mul_left_cancel₀ h0 (h1.trans h2.symm)
  have hemb_sub : ∀ ξ η, emb (ξ - η) = emb ξ - emb η := by
    intro ξ η; rw [hemb]; funext i; simp [map_sub]
  have he_sub : ∀ ξ η y, e (ξ - η) y = e ξ y * (starRingEnd ℂ) (e η y) := by
    intro ξ η y
    simp only [he]
    rw [hconj, hemb_sub, sub_dotProduct, sub_eq_add_neg, AddChar.map_add_eq_mul]
  have hsum_e : ∀ y, Summable fun ξ => ‖a ξ * e ξ y‖ := fun y => by simpa [norm_mul, he_norm] using hsum
  have hg_bd : ∀ y, ‖g y‖ ≤ ∑' ξ, ‖a ξ‖ := fun y => by
    rw [hg]
    refine (norm_tsum_le_tsum_norm (hsum_e y)).trans (le_of_eq ?_)
    congr 1; funext ξ; rw [norm_mul, he_norm, mul_one]
  have hg_cont : Continuous g := by
    rw [hg]
    exact continuous_tsum (fun ξ => continuous_const.mul (he_cont ξ)) hsum
      (fun ξ y => by rw [norm_mul, he_norm, mul_one])
  have h1 : ∀ y, ‖GlobalTheory.WeilM.thetaSum F (GlobalTheory.WeilM.schr ψ (x, y) Φ)‖ₑ = ‖g y‖ₑ := by
    intro y
    have : GlobalTheory.WeilM.thetaSum F (GlobalTheory.WeilM.schr ψ (x, y) Φ) = ψ (⅟2 * (x ⬝ᵥ y)) * g y := by
      rw [hg, ← tsum_mul_left]
      unfold GlobalTheory.WeilM.thetaSum GlobalTheory.WeilM.schr
      congr 1; funext ξ
      subst ha he hemb
      simp only [AddChar.map_add_eq_mul]; ring
    rw [this, enorm_mul, ← ofReal_norm_eq_enorm (ψ _), hnorm, ENNReal.ofReal_one, one_mul]
  have hgsq_int : Integrable (fun y => ‖g y‖ ^ 2) (μ.restrict 𝓕₁) :=
    Integrable.of_bound (hg_cont.norm.pow 2).aestronglyMeasurable ((∑' ξ, ‖a ξ‖) ^ 2) (ae_of_all _ fun y => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ (norm_nonneg _) (hg_bd y) 2)
  have lhs : ∫⁻ y in 𝓕₁, ‖GlobalTheory.WeilM.thetaSum F (GlobalTheory.WeilM.schr ψ (x, y) Φ)‖ₑ ^ 2 ∂μ =
      ENNReal.ofReal (∫ y in 𝓕₁, ‖g y‖ ^ 2 ∂μ) := by
    rw [ofReal_integral_eq_lintegral_ofReal hgsq_int (ae_of_all _ fun y => sq_nonneg _)]
    refine lintegral_congr fun y => ?_
    rw [h1, ← ofReal_norm_eq_enorm, ENNReal.ofReal_pow (norm_nonneg _)]
  have hcomp : ∀ y, ((‖g y‖ ^ 2 : ℝ) : ℂ) =
      ∑' p : (κ → F) × (κ → F), a p.1 * (starRingEnd ℂ) (a p.2) * e (p.1 - p.2) y := by
    intro y
    rw [Complex.ofReal_pow, ← Complex.mul_conj']
    simp only [hg]
    rw [Complex.conj_tsum, tsum_mul_tsum_of_summable_norm (hsum_e y) (by simpa [norm_mul, he_norm] using hsum)]
    congr 1; funext p
    rw [he_sub, map_mul]; ring
  have hFint : ∀ p : (κ → F) × (κ → F),
      Integrable (fun y => a p.1 * (starRingEnd ℂ) (a p.2) * e (p.1 - p.2) y) (μ.restrict 𝓕₁) := fun p =>
    (Integrable.of_bound (he_cont _).aestronglyMeasurable 1 (ae_of_all _ fun y => (he_norm _ _).le)).const_mul _
  have hnormint : ∀ p : (κ → F) × (κ → F),
      ∫ y in 𝓕₁, ‖a p.1 * (starRingEnd ℂ) (a p.2) * e (p.1 - p.2) y‖ ∂μ = ‖a p.1‖ * ‖a p.2‖ * μ.real 𝓕₁ := by
    intro p
    simp only [norm_mul, he_norm, RCLike.norm_conj, mul_one]
    rw [setIntegral_const, smul_eq_mul]; ring
  have hsumint : Summable fun p : (κ → F) × (κ → F) =>
      ∫ y in 𝓕₁, ‖a p.1 * (starRingEnd ℂ) (a p.2) * e (p.1 - p.2) y‖ ∂μ := by
    simp_rw [hnormint]
    exact (hsum.mul_of_nonneg hsum (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)).mul_right _
  have horth : ∀ ζ : κ → F, ∫ y in 𝓕₁, e ζ y ∂μ = if ζ = 0 then (μ.real 𝓕₁ : ℂ) else 0 := by
    intro ζ
    split_ifs with hζ
    · subst hζ
      have : ∀ y, e 0 y = 1 := fun y => by simp [he, hemb]
      simp_rw [this]; rw [setIntegral_const]; simp
    · obtain ⟨i, hi⟩ : ∃ i, ζ i ≠ 0 := by
        by_contra h; push_neg at h; exact hζ (funext h)
      haveI : Countable (GlobalTheory.ThetaParseval.ratVec F κ) := by
        refine Function.Surjective.countable (f := fun ρ : κ → F => (⟨emb ρ, ?_⟩ : GlobalTheory.ThetaParseval.ratVec F κ)) ?_
        · exact (GlobalTheory.ThetaParseval.mem_ratVec_iff _).2 ⟨ρ, by rw [hemb]⟩
        · rintro ⟨r, hr⟩
          obtain ⟨ρ, rfl⟩ := (GlobalTheory.ThetaParseval.mem_ratVec_iff r).1 hr
          exact ⟨ρ, by subst hemb; rfl⟩
      refine setIntegral_eq_zero_of_twist μ (GlobalTheory.ThetaParseval.ratVec F κ) hF (h := e ζ) ?_
        (c := Pi.single i (algebraMap F (AF F) (ζ i)⁻¹ * s0)) (a := ψ s0) ?_ hs0
      · intro r hr y
        obtain ⟨ρ, rfl⟩ := (GlobalTheory.ThetaParseval.mem_ratVec_iff r).1 hr
        simp only [he, dotProduct_add, AddChar.map_add_eq_mul]

        rw [show emb ζ ⬝ᵥ (fun i => algebraMap F (AF F) (ρ i)) = algebraMap F (AF F) (ζ ⬝ᵥ ρ) by
        subst hemb; simp [dotProduct, map_sum, map_mul], htriv, one_mul]
      · intro y
        simp only [he, dotProduct_add, AddChar.map_add_eq_mul]
        congr 2
        rw [dotProduct_single, hemb]
        simp only
        rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ hi, map_one, one_mul]
  have hFval : ∀ p : (κ → F) × (κ → F), ∫ y in 𝓕₁, a p.1 * (starRingEnd ℂ) (a p.2) * e (p.1 - p.2) y ∂μ =
      if p.1 = p.2 then ((‖a p.1‖ ^ 2 * μ.real 𝓕₁ : ℝ) : ℂ) else 0 := by
    intro p
    rw [integral_const_mul, horth]
    by_cases h : p.1 = p.2
    · rw [if_pos (sub_eq_zero.mpr h), if_pos h, h, Complex.mul_conj']; push_cast; ring
    · rw [if_neg (sub_ne_zero.mpr h), if_neg h, mul_zero]
  have hI : ∫ y in 𝓕₁, ‖g y‖ ^ 2 ∂μ = (∑' ξ, ‖a ξ‖ ^ 2) * μ.real 𝓕₁ := by
    apply Complex.ofReal_injective
    rw [← integral_complex_ofReal]
    simp_rw [hcomp]
    rw [← integral_tsum_of_summable_integral_norm hFint hsumint]
    simp_rw [hFval]
    have hinj : Function.Injective (fun ξ : κ → F => (ξ, ξ)) := fun _ _ h => (Prod.ext_iff.1 h).1
    rw [← hinj.tsum_eq]
    · simp only [if_true]
      rw [← tsum_mul_right, Complex.ofReal_tsum]
    · intro p hp
      by_cases h : p.1 = p.2
      · exact ⟨p.1, Prod.ext rfl h⟩
      · exact absurd (if_neg h) hp
  have hsq : Summable fun ξ => ‖a ξ‖ ^ 2 :=
    Summable.of_nonneg_of_le (fun _ => sq_nonneg _)
      (fun ξ => by
        rw [sq]
        exact mul_le_mul_of_nonneg_right (hsum.le_tsum ξ (fun _ _ => norm_nonneg _)) (norm_nonneg _))
      (hsum.mul_left (∑' ξ, ‖a ξ‖))
  rw [lhs, hI, ENNReal.ofReal_mul (tsum_nonneg fun _ => sq_nonneg _), ofReal_measureReal hfin, mul_comm,
    ENNReal.ofReal_tsum_of_nonneg (fun _ => sq_nonneg _) hsq]
  congr 1
  refine tsum_congr fun ξ => ?_
  rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm, ha, hemb]

end GlobalTheory.ThetaParsevalInner
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open MeasureTheory


theorem _root_.GlobalTheory.T.diagonalThetaSum_rationalPair_invariant : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsCharAF F ψ → ∀ (κ : Type) [Fintype κ]
    (Φ : (κ ⊕ κ → AF F) → ℂ), ∀ γ ∈ GlobalTheory.WeilUnitaryTransport.ratPair F κ, ∀ w : (κ → AF F) × (κ → AF F),
      GlobalTheory.WeilM.thetaSum F (GlobalTheory.WeilM.schr ψ (Sum.elim (γ + w).1 (γ + w).1, Sum.elim (γ + w).2 (-(γ + w).2)) Φ) =
        GlobalTheory.WeilM.thetaSum F (GlobalTheory.WeilM.schr ψ (Sum.elim w.1 w.1, Sum.elim w.2 (-w.2)) Φ) := by
  first | exact @GlobalTheory.DiagThetaRatInv.diag_theta_rat_inv | exact GlobalTheory.DiagThetaRatInv.diag_theta_rat_inv | (intros; apply GlobalTheory.DiagThetaRatInv.diag_theta_rat_inv <;> assumption)
end
