module

public import Formalism.LocalToGlobal.Columns.Bundle013
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle142
public import Formalism.LocalToGlobal.Columns.ToHLatLemmas
public import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffSetIntegralNat
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSmoothAutomorphicFunctionTranslateAtRealPlace
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IdemOfIsPrimeIdem
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle156
public import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle013
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsIsometryTriangularPeriodsOfFramePointMove
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle157
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle158
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle014
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle035
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle057
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle046
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle029
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle028
public import Formalism.LocalToGlobal.ProjectiveLattices.UnifDom
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle042
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1833
public import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1800
public import Formalism.SharpRestriction.Divisibility.WeightDegreeSizes
public import Formalism.SharpRestriction.ParamsHeightRankConstant
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1832
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
import Mathlib.Data.Nat.Choose.Multinomial
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IsClassSumPairingFormsLat
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle052
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsStabForm
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle154
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle045
import Development.AbelianVarietyTheory.Definitions.Foundations.ThetaSeriesTies
import Development.AbelianVarietyTheory.Definitions.Jets.EmbShortThLeThetaPlain
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.KernelSpanOverClasses
import Formalism.LocalToGlobal.IndefiniteForms.IndefSide
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.IndefiniteTreeX
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Formalism.LocalToGlobal.IndefiniteReal.Bundle001
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.SharpRestriction.Divisibility.AbelianOpenPart.AbelianAt

@[expose] public section

section

open Module NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Col Matrix
open scoped ComplexOrder
open Formalism.DivisionValues GlobalTheory.IndefiniteRowSideFullHecke

namespace GlobalTheory.ClassSumCoord

theorem ipAt_eq_gram : ∀ {K : Type} [Field K] [NumberField K] [StarRing K] (T : Formalism.L2.Col.GSD K) (h : T.Ok), T.Rat → ∀ (v : InfinitePlace K) (φ : T.EqFun), T.ipAt h v φ.1 φ.1 = star (fun i => v.embedding ((T.toCSD h).basis.equivFun (T.res h φ) i)) ⬝ᵥ ((T.toCSD h).H.map v.embedding *ᵥ fun i => v.embedding ((T.toCSD h).basis.equivFun (T.res h φ) i)) := by
  intro K _ _ _ T h R v φ
  letI := h.fintypeCl
  have hRc : (T.toCSD h).Rat := T.toCSDOf_rat h R T.outSec
  have hb := csd_hasRatBasis _ hRc
  have e : GlobalTheory.PeriodClassSum.coordAt T v φ.1 = GlobalTheory.PeriodOnStep.coAt (T.toCSD h) v (T.res h φ).1 := rfl
  rw [GlobalTheory.PeriodClassSum.ipAt_eq, e, GlobalTheory.PeriodOnStep.H_map _ v hb, GlobalTheory.PeriodOnStep.wForm_sum,
    GlobalTheory.PeriodOnStep.coAt_sum (T.toCSD h) v (T.res h φ)]
  simp only [Basis.equivFun_apply]
  rfl

end GlobalTheory.ClassSumCoord
end

section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.UnifEvery

open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Mult
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar}

theorem isUnit_gramAt (M : DSModel V S) (τ : D.what₂.Tau) : IsUnit (gramAt D V τ) := by
  rw [← M.fr_gram τ]
  have hJ : IsUnit (Formalism.REAL.Jm (M.ε τ)) := by
    unfold Formalism.REAL.Jm
    rw [Matrix.isUnit_diagonal, Pi.isUnit_iff]
    intro i
    split_ifs <;> simp
  exact (((Matrix.isUnit_conjTranspose _).2 (M.fr_unit τ)).mul hJ).mul (M.fr_unit τ)

theorem rep_mul (M : DSModel V S) (τ : D.what₂.Tau) {a b : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (ha : a ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) (hb : b ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) (w : M.H τ) :
    M.rep τ (a * b) w = M.rep τ a (M.rep τ b w) := by
  have hu : IsUnit (M.fr τ).det := (Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ)
  have h := (M.ds τ).2.2.1.1.2 _ (GlobalTheory.GardingVec.conj_mem (M.fr_unit τ) (M.fr_gram τ) ha) _
    (GlobalTheory.GardingVec.conj_mem (M.fr_unit τ) (M.fr_gram τ) hb)
  have e : M.fr τ * (a * b) * (M.fr τ)⁻¹ = M.fr τ * a * (M.fr τ)⁻¹ * (M.fr τ * b * (M.fr τ)⁻¹) := by
    simp only [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ hu]
  unfold DSModel.rep
  rw [e, h]
  rfl

theorem prod_mul_eq {G : Type} [Monoid G] (h : G) : ∀ (k : ℕ) (u v : Fin k → G), (∀ i, u i * h = h * v i) →
    (List.ofFn u).prod * h = h * (List.ofFn v).prod
  | 0, _, _, _ => by simp
  | k + 1, u, v, e => by
    rw [List.ofFn_succ, List.ofFn_succ, List.prod_cons, List.prod_cons, mul_assoc,
      prod_mul_eq h k _ _ fun i => e i.succ, ← mul_assoc, e, mul_assoc]

theorem rep_mem_sm (M : DSModel V S) (τ : D.what₂.Tau) {g : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hg : g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) {v : M.H τ} (hv : v ∈ M.sm τ) : M.rep τ g v ∈ M.sm τ := by
  have hG := isUnit_gramAt M τ
  have hgu : IsUnit g.det := by
    have h1 : IsUnit (gᴴ * gramAt D V τ * g) := by rw [show gᴴ * gramAt D V τ * g = _ from hg]; exact hG
    rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_mul] at h1
    exact isUnit_of_mul_isUnit_right h1
  have hab : g * g⁻¹ = 1 := Matrix.mul_nonsing_inv g hgu
  induction hv using Submodule.span_induction with
  | mem w hw =>
    refine Submodule.subset_span fun k Xs hX => ?_
    have hX' : ∀ i, g⁻¹ * Xs i * g ∈ lieAt V τ := fun i => GlobalTheory.Mem.RealTranslate.skew_conj hg hab (hX i)
    have h1 := ((M.rep τ g).restrictScalars ℝ).contDiff.comp (hw k (fun i => g⁻¹ * Xs i * g) hX')
    have hm : ∀ (Y : Fin k → Matrix (Fin V.rank) (Fin V.rank) ℂ), (∀ i, Y i ∈ lieAt V τ) → ∀ t : Fin k → ℝ,
        (List.ofFn fun i => NormedSpace.exp (t i • Y i)).prod ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ) := fun Y hY t =>
      GlobalTheory.GardingVec.list_prod_mem _ fun x hx => by
        obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hx
        exact GlobalTheory.GardingVec.exp_mem hG (hY i) (t i)
    convert h1 using 1
    funext t
    show _ = M.rep τ g (M.rep τ _ w)
    rw [← rep_mul M τ (hm Xs hX t) hg, ← rep_mul M τ hg (hm _ hX' t),
      prod_mul_eq g k _ _ fun i => GlobalTheory.Mem.RealTranslate.exp_conj_eq hab (Xs i) (t i)]
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul a x _ hx => rw [map_smul]; exact Submodule.smul_mem _ a hx

variable (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ))


variable {θ} {M : DSModel V S}

end GlobalTheory.UnifEvery
end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta
open Formalism.IndefR Formalism.IndefR.Mult Formalism.IndefR.Lev
open scoped TensorProduct

namespace GlobalTheory.HeckeKeepsGood

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

variable {V : HSp D} {β : GL (Fin V.rank) (EAf D)} {L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank}

theorem levChi_mul {k k' : GA D V} (hk : k ∈ levG V β L) (hk' : k' ∈ levG V β L) :
    levChi V β L (k * k') = levChi V β L k * levChi V β L k' := by
  unfold levChi
  rw [← Units.val_mul, MonoidHom.map_mul]
  exact congrArg Units.val ((Formalism.L2.DIV.levChar D.sp.cm V.gram β L).map_mul ⟨_, hk.2⟩ ⟨_, hk'.2⟩)

variable {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)} {N : ℕ}
  {Sb : Finset (HeightOneSpectrum (𝓞 D.host.F))} {P : HeightOneSpectrum (𝓞 D.host.E)} {d : List ℤ} {R : Finset (GA D V)}

theorem hasType_heckeLin (hB : IsBaseFrame V β Λ N) (hN : ((N : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal)
    (hPP : ∀ PP, PP ∈ L.Pg ∨ PP ∈ L.Q → PP ≠ P ∧ ¬ IsConjPl PP P)
    (hR : Hecke₂ V (levG V β L : Set (GA D V)) (levChi V β L) Sb P d R) {F : GA D V → ℂ}
    (hF : HasType V β L F) : HasType V β L (heckeLin V R F) :=
  GlobalTheory.SphericalOps.level_heckeLin (fun _ hk _ hk' => levChi_mul hk hk')
    (fun e f _ hI => ((GlobalTheory.LevSplit.lev_split V β Λ N L hB).2 P e f hI hN hPP).2.2) hR hF

theorem sphericalOperator_commute_levelFiniteGroup (hB : IsBaseFrame V β Λ N) (hN : ((N : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal)
    (hPP : ∀ PP, PP ∈ L.Pg ∨ PP ∈ L.Q → PP ≠ P ∧ ¬ IsConjPl PP P)
    (hR : Hecke₂ V (levG V β L : Set (GA D V)) (levChi V β L) Sb P d R) {F : GA D V → ℂ}
    (hF : HasType V β L F) (x : Formalism.L2.DIV.G0 L.Pg L.r) :
    actG0 V β L x (heckeLin V R F) = heckeLin V R (actG0 V β L x F) := by
  have hG := hasType_heckeLin hB hN hPP hR hF
  obtain ⟨e, f, ϖ, α, -, hI, -, -, -, hJ, hχ, -, -, hRs, -⟩ := hR
  unfold actG0
  split_ifs with hk
  swap
  · exact (map_zero _).symm
  have hκ := hk.choose_spec
  generalize hk.choose = κ at hκ ⊢
  obtain ⟨a1, -, a3⟩ := (GlobalTheory.LevSplit.lev_split V β Λ N (flagL L) hB).2 P e f hI hN hPP
  obtain ⟨k₁, m₁, k₂, -, s₁, s₂, rfl⟩ := a3 κ ⟨hκ.1, hκ.2.1, Subgroup.mem_top _⟩
  have m : k₁ ∈ levG V β L := (hJ k₁ s₁).2 ((a1 k₁ s₁).1 m₁)
  obtain ⟨hff, hcf, -⟩ := (GlobalTheory.T.supported_subgroup_split_commute_primeIdempotents V).2.2.1 P e f hI
  have hc : ∀ a, SuppF V f a → Commute a k₂ := fun a ha =>
    ((GlobalTheory.T.supported_subgroup_split_commute_primeIdempotents V).1 f hff hcf).2.2 (1 - f) a k₂ (by rw [mul_sub, mul_one, hff, sub_self]) ha s₂
  have key : ∀ G : GA D V → ℂ, HasType V β L G → ∀ h, G (h * (k₁ * k₂)) = G (h * k₂) := fun G hG h => by
    rw [(hc k₁ s₁).eq, ← mul_assoc, hG k₁ m, hχ k₁ m s₁, one_mul]
  funext h
  rw [key _ hG]
  show _ * ∑ γ ∈ R, F (h * k₂ * γ) = ∑ γ ∈ R, _ * F (h * γ * (k₁ * k₂))
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun γ hγ => ?_
  rw [key F hF, mul_assoc h γ, (hc γ (hRs γ hγ)).eq, mul_assoc h]

end GlobalTheory.HeckeKeepsGood
end
end

section

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HeckeOffLevel

variable {D : D7}

theorem sep_of_offS {S : Finset (HeightOneSpectrum (𝓞 D.host.F))} {Q PP : HeightOneSpectrum (𝓞 D.host.E)}
    (hS : OffS D S Q) (hP : (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) ∈ S) : PP ≠ Q ∧ ¬ Lev.IsConjPl PP Q := by
  obtain ⟨x, hx, hQ⟩ := hS _ hP
  have hx' : algebraMap (𝓞 D.host.F) (𝓞 D.host.E) x ∈ PP.asIdeal := hx
  refine ⟨fun h => hQ (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) x) rfl (h ▸ hx'), fun h => ?_⟩
  obtain ⟨c, hc, e⟩ := h _ hx'
  exact hQ c (e.trans ((D.sp.cm.fixed _).2 ⟨x, rfl⟩)) hc

variable {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)} {L : LevDat D.host.E ℂ V.rank}

theorem levChi_mul : ∀ k ∈ Lev.levG V β L, ∀ k' ∈ Lev.levG V β L,
    Lev.levChi V β L (k * k') = Lev.levChi V β L k * Lev.levChi V β L k' := by
  intro k hk k' hk'
  unfold Lev.levChi
  rw [MonoidHom.map_mul, ← Units.val_mul]
  exact congrArg Units.val ((levChar D.sp.cm V.gram β L).map_mul ⟨_, hk.2⟩ ⟨_, hk'.2⟩)

variable {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)} {N : ℕ}
  {S : Finset (HeightOneSpectrum (𝓞 D.host.F))} {Q : HeightOneSpectrum (𝓞 D.host.E)} {d : List ℤ} {Rp : Finset (GA D V)}

theorem hasType_heckeLin (hB : Lev.IsBaseFrame V β Λ N) (hN : ((N : ℕ) : 𝓞 D.host.E) ∉ Q.asIdeal)
    (hP : ∀ PP, PP ∈ L.Pg ∨ PP ∈ L.Q → PP ≠ Q ∧ ¬ Lev.IsConjPl PP Q)
    (h : Hecke₂ V (Lev.levG V β L : Set (GA D V)) (Lev.levChi V β L) S Q d Rp) {Φ : GA D V → ℂ}
    (hΦ : Lev.HasType V β L Φ) : Lev.HasType V β L (heckeLin V Rp Φ) :=
  GlobalTheory.SphericalOps.level_heckeLin levChi_mul
    (fun e f _ hi => ((GlobalTheory.LevSplit.lev_split V β Λ N L hB).2 Q e f hi hN hP).2.2) h hΦ

end GlobalTheory.HeckeOffLevel
end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.L2.Pj Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PrimIn

theorem _root_.GlobalTheory.T.injective_complexCoords_principalLevel : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T0 : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3), A3.fam3.Ok3 1 → R.WeakCharacterisation F → (R.toCx3 F).zs.InBlock → ∀ t, Function.Injective ((R.toCx3 F).iC (crdOf3 A3 ⊥ 1 F.P1 F.ψ1 F.Dc F.Sp F.Zsc) false t) := by
  first | exact @GlobalTheory.PrimIn.iC_principal_injective | exact GlobalTheory.PrimIn.iC_principal_injective | (intros; apply GlobalTheory.PrimIn.iC_principal_injective <;> assumption)
end

section

open NumberField AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
  ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.LevelCusp
open GlobalTheory.Dict (castFr)
open scoped Matrix

noncomputable section

namespace GlobalTheory.CongrOrbit



theorem exists_congr_back : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l) (c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Formalism.L2.PjFree.Unf Xo c σ r), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → l.A = 1 → 1 ≤ r → ∀ k, ∀ γ ∈ (U.X k).Γ, ∀ x ∈ (U.X k).dom, ∃ η : GL (Fin r) E, ReciprocityTheory.ChartRestriction.G.FD.IsUStab (U.X k).Gm (U.X k).Λ η ∧ (∀ w ∈ (U.X k).Λ, ∃ y ∈ (U.X k).Λ, Matrix.mulVec (η : Matrix (Fin r) (Fin r) E) w - w = (l.M : E) • y) ∧ ∃ b ∈ ReciprocityTheory.ChartRestriction.G.FD.Bor (U.X k).Ψ r, x = ReciprocityTheory.ChartRestriction.G.FD.rmul (ReciprocityTheory.ChartRestriction.G.FD.lact η (ReciprocityTheory.ChartRestriction.G.FD.lact γ x)) b := by
  classical
  intro E _ _ _ H Dw l Xo c σ r U hσ hU hA _hr k γ hγ x hx
  have hx' : lact γ x ∈ (U.X k).dom := dom_lact (U.X k) hx ((U.X k).Γ_stab γ hγ)

  let b₁ : Frame (U.X k).Ψ r := fun _ => (1 : Matrix (Fin r) (Fin r) ℂ)
  have hm₁ : ∀ τ, mat b₁ τ = 1 := fun τ => rfl
  have hb₁ : b₁ ∈ Bor (U.X k).Ψ r := fun τ => ⟨by rw [hm₁]; simp, fun a c hca => by
    have := hm₁ τ
    change Matrix.of (b₁ τ) = 1 at this
    have h2 := congrFun (congrFun this a) c
    simpa [Matrix.one_apply_ne (ne_of_gt hca)] using h2⟩
  have hrm : rmul (lact γ x) b₁ = lact γ x := by
    funext τ
    change mat (lact γ x) τ * mat b₁ τ = lact γ x τ
    rw [hm₁, Matrix.mul_one]
    rfl
  obtain ⟨t, hB⟩ : ∃ t : Ix Dw → (CAt σ)ˣ, FrBor t (U.un k ⟨x, hx⟩) (U.un k ⟨lact γ x, hx'⟩) :=
    (hU.2.2.2.1 k k ⟨x, hx⟩ ⟨lact γ x, hx'⟩).2 ⟨γ, hγ, b₁, hb₁, by rw [hrm]⟩
  obtain ⟨hrr, hty, -, -, -, g, e, F, ik, φ, hEF, hpt⟩ := hU
  obtain ⟨P, hP, p, hPx, hv, -⟩ := hpt k ⟨x, hx⟩
  obtain ⟨P', hP', p', hPx', hv', -⟩ := hpt k ⟨lact γ x, hx'⟩
  have hu : F.u (ik k) P' = F.u (ik k) P := by rw [← hPx, ← hPx', hB.1]
  obtain ⟨h, gam, hex, hh, hiso, hM, -⟩ := GlobalTheory.T.familyUnif_exp_unique_alt E H Dw l Xo _ g _ F (ik k) (ik k) P' P p' p hu

  have hM' : ∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) (F.Di (ik k)).La),
      ∃ e, gam a = a + l.M • e := by
    intro a ha
    refine Submodule.smul_induction_on ha ?_ ?_
    · intro v hv b _
      obtain ⟨c, e, rfl⟩ := F.t_surj (ik k) b
      obtain ⟨e₁, he₁⟩ := hM (v • c) (Submodule.smul_mem_smul hv Submodule.mem_top)
      obtain ⟨r, hr⟩ : l.M ∣ l.M' := Nat.dvd_lcm_left _ _
      refine ⟨e₁ + r • (gam (v • e) - v • e), ?_⟩
      rw [smul_add, ← map_smul, smul_comm v, map_add (f := _), he₁, map_nsmul, hr, smul_add, smul_smul,
        smul_sub]
      abel
    · rintro x y ⟨e, he⟩ ⟨e', he'⟩
      exact ⟨e + e', by rw [map_add (f := _), he, he', smul_add]; abel⟩
  have f₁ := GlobalTheory.LevelHalf.trivial_mod_of_trivial_on_half E H (F.Di (ik k)) l gam hiso hM'

  choose cf hcf1 hcf2 hcf3 using hB.2.1
  have hcol : ∀ τ i, h.toLinearMap (Pi.single (e.symm ⟨τ, i⟩) 1) =
      (∑ j, (show ℂ from cf τ i j) • (Pi.single (e.symm ⟨τ, j⟩) 1 : Fin g → ℂ)) := by
    intro τ i
    have d1 := (DerLin.isCombAt_iff_isDerivAt0 E H Dw l Xo _ g _ F _ P p _ ((U.un k ⟨x, hx⟩).u τ) _ (hv τ)
      (cf τ i) ((U.un k ⟨lact γ x, hx'⟩).u τ i)).1 (hPx ▸ hcf3 τ i)
    have d0 := hv' τ i
    simp only [← hex] at d0
    have d2 := (ExpChain.isDerivAt0_comp_linear _ (ExpChain.isHolTo_ex F _ P p) h.toLinearMap _ _).1 d0
    have tn := isDerivAt0_ex_isTanAt E H Dw l Xo _ g _ F _ P p
    exact (tn.2.2 _ (tn.1 _ _ d2)).unique d2 d1
  let gm : (U.X k).Λ ≃ₗ[𝓞 E] (U.X k).Λ := (φ k).symm ≪≫ₗ gam ≪≫ₗ φ k
  let A : (E →+* ℂ) → ℕ → ℕ → ℂ := fun τ i j =>
    if hij : i < Dw.mult τ ∧ j < Dw.mult τ then Formalism.L2.PjFree.toC (cf τ ⟨j, hij.2⟩ ⟨i, hij.1⟩) else 0
  have hA0 : ∀ τ i j, j < i → A τ i j = 0 := by
    intro τ i j hji
    simp only [A]
    split_ifs with hij
    · exact hcf2 τ _ _ hji
    · rfl
  have hAr : ∀ τ, ∀ i < Dw.mult τ, ∀ v : (U.X k).Λ,
      Formalism.L2.PjFree.perFr (U.X k) x (gm v : Fin r → E) (Formalism.L2.PjFree.relab c σ τ) i =
        ∑ j ∈ Finset.range (Dw.mult τ), A τ i j *
          Formalism.L2.PjFree.perFr (U.X k) (lact γ x) (v : Fin r → E) (Formalism.L2.PjFree.relab c σ τ) j := by
    intro τ i hi v
    obtain ⟨v, rfl⟩ := (φ k).surjective v
    simp only [gm, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
    have a1 := hP (gam v) (e.symm ⟨τ, ⟨i, hi⟩⟩)
    rw [Equiv.apply_symm_apply] at a1
    rw [← a1, hh, Finset.sum_range]
    refine (apply_of_cols e h.toLinearMap (fun τ i j => cf τ i j) hcol (P' v) τ ⟨i, hi⟩).trans
      (Finset.sum_congr rfl fun j _ => ?_)
    rw [hP', Equiv.apply_symm_apply]
    simp only [A]
    rw [dite_eq_left ⟨hi, j.2⟩]
    rfl
  have hgiso : ∀ u v : (U.X k).Λ, Algebra.trace ℚ E (-(U.X k).ξ0 * herm (U.X k).Gm (gm u : Fin r → E)
      (gm v : Fin r → E)) = Algebra.trace ℚ E (-(U.X k).ξ0 * herm (U.X k).Gm (u : Fin r → E) (v : Fin r → E)) := by
    intro u v
    obtain ⟨u, rfl⟩ := (φ k).surjective u
    obtain ⟨v, rfl⟩ := (φ k).surjective v
    simp only [gm, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
    rw [← hEF, ← hEF, hiso]

  obtain ⟨η, ε, -, hξ, hav, hlat, hisoη⟩ := GlobalTheory.T.exists_rational_isometry_of_trace_isometry E r (U.X k) (U.X k) (fun _ => rfl) gm hgiso
  have hε : ε = 1 := mul_right_cancel₀ (U.X k).ξ0_ne (hξ.symm.trans (one_mul _).symm)
  have hUS : IsUStab (U.X k).Gm (U.X k).Λ η := ⟨fun u v => by rw [hisoη, hε, one_mul], hlat⟩
  have hcong : ∀ w ∈ (U.X k).Λ, ∃ y ∈ (U.X k).Λ,
      (η : Matrix (Fin r) (Fin r) E) *ᵥ w - w = (l.M : E) • y := by
    intro w hw
    obtain ⟨a, ha⟩ := (φ k).surjective ⟨w, hw⟩
    obtain ⟨e₀, he₀⟩ := f₁ a
    refine ⟨(φ k e₀ : Fin r → E), (φ k e₀).2, ?_⟩
    have h1 := hav ⟨w, hw⟩
    have h2 : gm ⟨w, hw⟩ = ⟨w, hw⟩ + l.M • φ k e₀ := by
      simp only [gm, LinearEquiv.trans_apply, ← ha, LinearEquiv.symm_apply_apply, he₀, map_add (f := _), map_nsmul]
    rw [h2] at h1
    change (η : Matrix (Fin r) (Fin r) E) *ᵥ w = _ at h1
    rw [h1]
    simp [Nat.cast_smul_eq_nsmul]

  obtain ⟨hbij, hrt, -, -⟩ := GlobalTheory.Relab.relab_good E H l c σ hσ
  let ρe := Equiv.ofBijective _ hbij
  have he : ∀ τ, Formalism.L2.PjFree.relab c σ (ρe.symm τ) = τ := ρe.apply_symm_apply
  have m1 : ∀ τ ∈ (U.X k).Ψ, Dw.mult (ρe.symm τ) = r - (U.X k).p0 := fun τ hτ => by
    unfold Datum.mult
    rw [if_pos ((hrt _).1 (by rw [he]; exact ((hty k).2 τ).1 hτ)), (hty k).1]
    omega
  have m2 : ∀ τ ∉ (U.X k).Ψ, Dw.mult (ρe.symm τ) = (U.X k).p0 := fun τ hτ => by
    unfold Datum.mult
    rw [if_neg (fun h => hτ (((hty k).2 τ).2 (by rw [← he τ]; exact (hrt _).2 h))), (hty k).1]
  have hrel : ∀ τ, ∀ i < Dw.mult (ρe.symm τ), ∀ v ∈ (U.X k).Λ,
      Formalism.L2.PjFree.perFr (U.X k) x ((η : Matrix (Fin r) (Fin r) E) *ᵥ v) τ i =
        ∑ j ∈ Finset.range (Dw.mult (ρe.symm τ)), A (ρe.symm τ) i j *
          Formalism.L2.PjFree.perFr (U.X k) (lact γ x) v τ j :=
    fun τ i hi v hv => by
      have := hAr (ρe.symm τ) i hi ⟨v, hv⟩
      rwa [he, ← hav] at this
  obtain ⟨b, hb, hxb, -⟩ := GlobalTheory.T.frames_differ_by_isometry_and_triangular_of_periods E r (U.X k) (U.X k) η (isMatch_of_isUStab (U.X k) hUS)
    (fun τ => Dw.mult (ρe.symm τ)) m1 m2 (lact γ x) hx' x hx (fun τ => A (ρe.symm τ))
    (fun τ => hA0 _) hrel
  exact ⟨η, hUS, hcong, b, hb, hxb⟩

end GlobalTheory.CongrOrbit
end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Datum Formalism.IndefR.Lev
open GlobalTheory.FormTies GlobalTheory.OnTies GlobalTheory.TraceClassRank
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OnCmp GlobalTheory.BigOn GlobalTheory.RealIndexBound
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)

theorem _root_.GlobalTheory.T.exists_coprime_mul_inv_genusLatticeScalar_integral : ∀ (D : D7) (T : Full D), LawsFull T → ∀ (j : ℕ), InR D j → ∀ {n : ℕ} (Λ : GenLat D.host.E n) (σ : T.Q.c.F →+* ℂ) (p : ℕ), p.Prime → Λ.Unimod → Λ.TrivAt (badN D) → Λ.TrivAt p → ∃ m : ℕ, Nat.Coprime m p ∧ IsIntegral ℤ ((m : ℂ) * (σ (betaH (Dw := T.Q.Dw j) T.Q.c Λ))⁻¹) := by
  first | exact @GlobalTheory.BetaInvIntegral.betaH_inv_integral | exact GlobalTheory.BetaInvIntegral.betaH_inv_integral | (intros; apply GlobalTheory.BetaInvIntegral.betaH_inv_integral <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Datum Formalism.IndefR.Lev
open GlobalTheory.FormTies GlobalTheory.OnTies GlobalTheory.TraceClassRank
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OnCmp GlobalTheory.BigOn GlobalTheory.RealIndexBound
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)

theorem _root_.GlobalTheory.T.exists_isIntegral_absNorm_pow_mul_onId_of_coprime : ∀ (E : Type) [Field E] [NumberField E] (ψ : Formalism.L2.Host.HChar E) (I : Type) [Fintype I] (φs : I → E →+* ℂ) (n : I → ℤ), ψ.HasInf φs n → (∀ v, ψ.TameAt v) → ∀ b : ℕ, b ≠ 0 → (∀ v : HeightOneSpectrum (𝓞 E), (b : 𝓞 E) ∉ v.asIdeal → ψ.UnrAt v) → ∀ cc : Ideal (𝓞 E), cc ≠ ⊥ → cc ⊔ Ideal.span {(b : 𝓞 E)} = ⊤ → ∃ K : ℕ, IsIntegral ℤ (((Ideal.absNorm cc : ℕ) : ℂ) ^ K * ((ψ.onId (cc : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) : ℂˣ) : ℂ)) := by
  first | exact @GlobalTheory.TameHeckeIntegral.isIntegral_absNorm_pow_mul_onId | exact GlobalTheory.TameHeckeIntegral.isIntegral_absNorm_pow_mul_onId | (intros; apply GlobalTheory.TameHeckeIntegral.isIntegral_absNorm_pow_mul_onId <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions NumberField Classical

namespace GlobalTheory

theorem admissibleConstants_closed_under_sizeBounds : ∀ (𝒞 : FamClass), (∀ {eps : ℝ} (Fm : FamP eps), 𝒞 Fm → TuSize Fm ∧ DGamSize Fm) →
    Closed 𝒞 (fun Fm _ => Formalism.MainNotions.WeightDegreeSizes.FamilySecondComplementInputs Fm) := by
  intro 𝒞 h𝒞
  refine ⟨1 / 100, by norm_num, fun eps he hle => ?_⟩
  have hK : Nonempty TransportedAlt := ⟨by constructor <;> exact 0⟩
  obtain ⟨K⟩ := hK
  refine ⟨K, fun Fm _ hc _ => ?_⟩
  have hlt : eps < 1 / 52 := lt_of_le_of_lt hle (by norm_num)
  exact GlobalTheory.T.admissibleComplementTwo_along_family Fm he hlt (h𝒞 Fm hc).1 (h𝒞 Fm hc).2

end GlobalTheory
end
