module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2406
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2445
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2446
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2418
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2442
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2447
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2426
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.LocalToGlobal.LatticeGeometry.CmTypeMeetsConjugatePair
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsLevFnPow
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle155
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle547
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle196
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemElt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2443
public import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.CoefFnEqZeroOfNotPos
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
import Mathlib.RingTheory.PicardGroup
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
import Development.AbelianVarietyTheory.BlockTheory.PoincareCuspForms.Bundle003
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle059
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
import Development.AbelianVarietyTheory.Definitions.ThetaValues.Bundle002
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.ExpTie GlobalTheory.ExpTie.Lift

theorem _root_.GlobalTheory.T.liftWeightRho_window_contains_cloud : ∀ {D : Formalism.BasicNotions.D7} (L : Formalism.BasicNotions.SizeData₂ D) (j : Fin D.R.m) (τ : D.what₂.Tau), GlobalTheory.ExpTie.Lift.ValsAt L j τ → ((GlobalTheory.ExpTie.Lift.wts L j).c τ ≤ ((GlobalTheory.ExpTie.Lift.wts L j).xm τ : ℝ) ∧ (GlobalTheory.ExpTie.Lift.wts L j).xm τ ≤ (GlobalTheory.ExpTie.Lift.wts L j).xp τ ∧ ((GlobalTheory.ExpTie.Lift.wts L j).xp τ : ℝ) ≤ (GlobalTheory.ExpTie.Lift.wts L j).c τ + (GlobalTheory.ExpTie.parOf L j).S) ∧ ∀ a, a < Formalism.CohomologicalDescent.ShortWeightBounds.kc (GlobalTheory.ExpTie.parOf L j) → (GlobalTheory.ExpTie.Lift.wts L j).xm τ ≤ (GlobalTheory.ExpTie.Lift.wts L j).U (GlobalTheory.ExpTie.parOf L j) τ a ∧ (GlobalTheory.ExpTie.Lift.wts L j).U (GlobalTheory.ExpTie.parOf L j) τ a ≤ (GlobalTheory.ExpTie.Lift.wts L j).xp τ := by
  first | exact @GlobalTheory.ExpTie.Lift.window_cloud | exact GlobalTheory.ExpTie.Lift.window_cloud | (intros; apply GlobalTheory.ExpTie.Lift.window_cloud <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.ExpTie GlobalTheory.ExpTie.Lift

theorem _root_.GlobalTheory.T.liftWeightRho_entries_le_floor_height : ∀ {D : Formalism.BasicNotions.D7} (L : Formalism.BasicNotions.SizeData₂ D) (P5 : Formalism.BasicNotions.ParameterChoice' D L) (j : Fin D.R.m) (τ : D.what₂.Tau), (GlobalTheory.ExpTie.parOf L j).Large → GlobalTheory.ExpTie.Lift.ValsAt L j τ → ∀ a, a < (GlobalTheory.ExpTie.parOf L j).Nr → (GlobalTheory.ExpTie.Lift.wts L j).U (GlobalTheory.ExpTie.parOf L j) τ a ≤ (Formalism.CohomologicalDescent.ShortWeightBounds.h0 (GlobalTheory.ExpTie.parOf L j) : ℤ) := by
  first | exact @GlobalTheory.ExpTie.Lift.wts_U_le_h0_of_large | exact GlobalTheory.ExpTie.Lift.wts_U_le_h0_of_large | (intros; apply GlobalTheory.ExpTie.Lift.wts_U_le_h0_of_large <;> assumption)
end

section

open NumberField IsDedekindDomain Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.CovTop Formalism.L2.Pj GlobalTheory.FormTies GlobalTheory.Shares
open ReciprocityTheory.ChartRestriction.G.PullbackSections.PfModelLatA GlobalTheory.ShareOn

theorem _root_.GlobalTheory.T.uniformisation_components_share_cmData : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz), More p → ∀ (r : TwoRuns p.T p.P.Gp) (h : RunsOk (fw2 p) r), OwnPin r → ∀ (i : Fin D.R.m) (v : HeightOneSpectrum (𝓞 D.what₂.LL)), ∀ k k' : (uAt r v i).Comp, ((uAt r v i).X k).Ψ = ((uAt r v i).X k').Ψ ∧ ((uAt r v i).X k).p0 = ((uAt r v i).X k').p0 ∧ ((uAt r v i).X k).Gm = ((uAt r v i).X k').Gm ∧ ((uAt r v i).X k).ξ0 = ((uAt r v i).X k').ξ0 := by
  first | exact @GlobalTheory.ShareOn.comps_share | exact GlobalTheory.ShareOn.comps_share | (intros; apply GlobalTheory.ShareOn.comps_share <;> assumption)
end

section

open NumberField IsDedekindDomain Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.CovTop Formalism.L2.Pj GlobalTheory.FormTies GlobalTheory.Shares
open ReciprocityTheory.ChartRestriction.G.PullbackSections.PfModelLatA GlobalTheory.ShareOn

theorem _root_.GlobalTheory.T.lattice_preserved_by_component_stabilizer : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz), More p → ∀ (r : TwoRuns p.T p.P.Gp) (h : RunsOk (fw2 p) r), OwnPin r → ∀ (i : Fin D.R.m) (v : HeightOneSpectrum (𝓞 D.what₂.LL)), ∀ (k : (uAt r v i).Comp), ∀ γ ∈ ((uAt r v i).X k).Γ, ∀ w ∈ lattice₂ D ((uAt r v i).X k).Λ, Matrix.mulVec (γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E) w - w ∈ p.T.Q.l.Mb • lattice₂ D ((uAt r v i).X k).Λ := by
  first | exact @GlobalTheory.ShareOn.sub_mem_half_smul_latP | exact GlobalTheory.ShareOn.sub_mem_half_smul_latP | (intros; apply GlobalTheory.ShareOn.sub_mem_half_smul_latP <;> assumption)
end

section

open NumberField IsDedekindDomain Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.CovTop Formalism.L2.Pj GlobalTheory.FormTies GlobalTheory.Shares
open ReciprocityTheory.ChartRestriction.G.PullbackSections.PfModelLatA GlobalTheory.ShareOn

theorem _root_.GlobalTheory.T.uniformisation_character_trivial_arithmeticGroup : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz), More p → ∀ (r : TwoRuns p.T p.P.Gp) (h : RunsOk (fw2 p) r), OwnPin r → ∀ (i : Fin D.R.m) (v : HeightOneSpectrum (𝓞 D.what₂.LL)), ∀ (k : (uAt r v i).Comp) (la : Wt ((uAt r v i).X k).Ψ D.R.r), ∀ γ ∈ ((uAt r v i).X k).Γ, ((uAt r v i).X k).χ la γ = 1 := by
  first | exact @GlobalTheory.ShareOn.uAt_chi_eq_one | exact GlobalTheory.ShareOn.uAt_chi_eq_one | (intros; apply GlobalTheory.ShareOn.uAt_chi_eq_one <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpFrame GlobalTheory.ExpTie GlobalTheory.FrameOf
open scoped TensorProduct

namespace GlobalTheory.FrameTriv

theorem map_eq_one_of_isLocEnv {D : D7} (V : Formalism.BasicNotions.TH.HSp D) {Pl0 : Type} (pl : Pl0 → HeightOneSpectrum (𝓞 D.host.E)) (ok : Set Pl0)
    (i : ok × ℕ) (x : Bridge.Gf V) (hloc : isLocEnv V pl ok i x) (l : ℕ) (hl : (l : 𝓞 D.host.E) ∉ (pl i.1).asIdeal)
    {R : Type} [CommRing R] (ev : (FiniteAdeleRing (𝓞 D.host.F) D.host.F) ⊗[D.host.F] D.host.E →+* R)
    (hev : ∀ a : FiniteAdeleRing (𝓞 D.host.F) D.host.F,
      (∀ v : HeightOneSpectrum (𝓞 D.host.F), (l : 𝓞 D.host.F) ∈ v.asIdeal → a v = 0) → ev (a ⊗ₜ[D.host.F] 1) = 0) :
    (x.1.val : Matrix (Fin V.rank) (Fin V.rank) ((FiniteAdeleRing (𝓞 D.host.F) D.host.F) ⊗[D.host.F] D.host.E)).map ev = 1 := by
  obtain ⟨e, α, he, -, hS, hx⟩ := hloc
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.IdemSupport.exists_comp D
  obtain ⟨-, ε, hε, hf⟩ := GlobalTheory.IdemSupport.of_isPrimeIdem hΦ (Or.inl ⟨he, rfl⟩)
  obtain ⟨εf, hεf, -, h0⟩ := hε
  have hvan : ev (εf ⊗ₜ[D.host.F] (1 : D.host.E)) = 0 := by
    refine hev εf fun v' hv' => h0 v' ?_
    rintro rfl
    apply hl
    have h2 : algebraMap (𝓞 D.host.F) (𝓞 D.host.E) (l : 𝓞 D.host.F) ∈ (pl i.1).asIdeal := hv'
    rwa [map_natCast] at h2
  let φ : Formalism.L2.Theta.AE D →+* (FiniteAdeleRing (𝓞 D.host.F) D.host.F) ⊗[D.host.F] D.host.E :=
    (Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sndA D.host.F) (AlgHom.id D.host.F D.host.E)).toRingHom
  have hmat : ∀ a c, x.1.val a c = φ ((Formalism.L2.Theta.mt V α) a c) := by
    intro a c
    rw [hx]
    rfl
  have hφε : φ (algebraMap _ (Formalism.L2.Theta.AE D) ε) = εf ⊗ₜ[D.host.F] (1 : D.host.E) := by
    rw [hεf]
    rfl
  let ψ : Formalism.L2.Theta.AE D →+* R := ev.comp φ
  have hψ : ψ (algebraMap _ (Formalism.L2.Theta.AE D) ε) = 0 := (congrArg ev hφε).trans hvan
  ext a c
  have hsplit : Formalism.L2.Theta.mt V α a c =
      algebraMap _ (Formalism.L2.Theta.AE D) ε * (Formalism.L2.Theta.mt V α - 1) a c + (1 : Matrix _ _ (Formalism.L2.Theta.AE D)) a c := by
    rw [← hf, hS a c, Matrix.sub_apply, sub_add_cancel]
  refine (congrArg ev (hmat a c)).trans ?_
  show ψ _ = _
  rw [hsplit, map_add ψ, ψ.map_mul, hψ, zero_mul, zero_add, Matrix.one_apply, Matrix.one_apply]
  split_ifs
  · exact ψ.map_one
  · exact ψ.map_zero

theorem intEmb_injective {l : ℕ} [Fact l.Prime] (Lf : IntermediateField ℚ_[l] (PadicAlgCl l)) : Function.Injective (intEmb Lf) :=
  fun _ _ h => Subtype.ext (Subtype.ext h)

theorem kap_eq_one {O K : Type} [CommRing O] [CommRing K] {f : O →+* K} (hf : Function.Injective f) {N n : ℕ} (g : GL (Fin N) O)
    (b : GL (Fin N) K) (M : Matrix (Fin n) (Fin n) K) (rk : Fin N → Fin n) (hrk : Function.Injective rk) (hM : M = 1)
    (h : (Matrix.GeneralLinearGroup.map f g).val = (b⁻¹).val * M.submatrix rk rk * b.val) : g = 1 := by
  rw [hM, Matrix.submatrix_one _ hrk, mul_one, Units.inv_mul] at h
  refine Units.ext (Matrix.ext fun a c => hf ?_)
  have h3 : f (g.val a c) = (1 : Matrix (Fin N) (Fin N) K) a c := congrFun (congrFun h a) c
  rw [h3, Units.val_one, Matrix.one_apply, Matrix.one_apply]
  split_ifs
  · exact f.map_one.symm
  · exact f.map_zero.symm

theorem chi_eq_one {O K ι : Type} [CommRing O] [Field K] [Fintype ι] {f : O →+* K} (hf : Function.Injective f) {N : ℕ}
    (io : K ≃+* ℂ) (g : ι → GL (Fin N) O) (sh : ι → ℤ) (x : Oˣ) (y : ℂˣ) (hg : g = 1) (hy : y = 1)
    (h : io (f x * ∏ τ, f (g τ).val.det ^ sh τ) * (y : ℂ) = 1) : x = 1 := by
  subst hg hy
  simp only [Pi.one_apply, Units.val_one, Matrix.det_one, map_one, one_zpow, Finset.prod_const_one, mul_one] at h
  refine Units.ext (hf (io.injective ?_))
  rw [h, Units.val_one, map_one, map_one]



theorem triv_of_isLocEnv : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz) (j : Fin D.R.m) (w : HeightOneSpectrum (𝓞 D.what₂.LL)) [Fact (Formalism.EigenvalueLevelCeiling.plc w).Prime] {N : ℕ} (e0 : D.what₂.LL →+* PadicAlgCl (Formalism.EigenvalueLevelCeiling.plc w)) (b : Bool) (io : PadicAlgCl (Formalism.EigenvalueLevelCeiling.plc w) ≃+* ℂ) (ev : D.what₂.Tau → ((FiniteAdeleRing (𝓞 D.host.F) D.host.F) ⊗[D.host.F] D.host.E →+* PadicAlgCl (Formalism.EigenvalueLevelCeiling.plc w))) (bs : D.what₂.Tau → GL (Fin N) (PadicAlgCl (Formalism.EigenvalueLevelCeiling.plc w))) (rk : Fin N ≃o Fin (Vc D j).rank) (sh : D.what₂.Tau → ℤ) (Lf : IntermediateField ℚ_[Formalism.EigenvalueLevelCeiling.plc w] (PadicAlgCl (Formalism.EigenvalueLevelCeiling.plc w))) [FiniteDimensional ℚ_[Formalism.EigenvalueLevelCeiling.plc w] Lf] (kap : levJ p j (p.R.mu w) →* (D.what₂.Tau → GL (Fin N) (intR Lf))) (chi : levJ p j (p.R.mu w) →* (intR Lf)ˣ), ChoiceOk p j w e0 b io ev bs rk sh kap chi → ∀ (i : (blk p j (p.R.mu w)).Pl × ℕ), 1 ≤ i.2 → i.2 ≤ (Vc D j).rank → ((Formalism.EigenvalueLevelCeiling.plc w : ℕ) : 𝓞 D.host.E) ∉ (plOf p j (p.R.mu w) i.1).asIdeal → ∀ u : Bridge.Gf (Vc D j), u ∈ levJ p j (p.R.mu w) → isLocEnv (Vc D j) p.R.pl (p.P.A3.A.ok (p.R.mu w)) i u → (frameOf p j (p.R.mu w) (Formalism.EigenvalueLevelCeiling.plc w) N Lf kap chi).Triv u := by
  intro D L hT Gi Gl Kc Y cX ex Csz p j w _ N e0 b io ev bs rk sh Lf _ kap chi hC i hi1 hi2 hl u hu hloc
  obtain ⟨-, -, -, hEv, hKap, hChi⟩ := hC
  have hc : levChi p j (p.R.mu w) ⟨u, hu⟩ = 1 := (p.R.B.L j (p.R.mu w)).hecke.chi_loc i ⟨hi1, hi2⟩ ⟨u, hu⟩ hloc
  have hone : ∀ τ, (matOf j u).map (ev τ) = 1 := fun τ =>
    map_eq_one_of_isLocEnv (Vc D j) p.R.pl (p.P.A3.A.ok (p.R.mu w)) i u hloc (Formalism.EigenvalueLevelCeiling.plc w) hl (ev τ) (hEv τ).2.2.1
  have hk : kap ⟨u, hu⟩ = 1 := funext fun τ =>
    kap_eq_one (intEmb_injective Lf) (kap ⟨u, hu⟩ τ) (bs τ) ((matOf j u).map (ev τ)) rk rk.injective (hone τ) (hKap ⟨u, hu⟩ τ)
  have hx : chi ⟨u, hu⟩ = 1 :=
    chi_eq_one (intEmb_injective Lf) io (kap ⟨u, hu⟩) sh (chi ⟨u, hu⟩) (levChi p j (p.R.mu w) ⟨u, hu⟩) hk hc (hChi ⟨u, hu⟩)
  exact ⟨hu, hk, hx⟩

end GlobalTheory.FrameTriv
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpFrame GlobalTheory.ExpTie GlobalTheory.FrameOf
open scoped TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HalfLabels

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {l : ℕ} [Fact l.Prime]

theorem cjE_cjE (φ : E →+* Formalism.ConjugateSelfDual.Qbar l) : ExpFrame.cj (cj φ) = φ := by
  ext x
  simp only [ExpFrame.cj, RingHom.comp_apply]
  exact congrArg φ (IsCMField.complexConj_apply_apply E x)

theorem isHalf_cj {ι : Type} {inc : ι → (E →+* Formalism.ConjugateSelfDual.Qbar l)} (h : IsHalf inc) : IsHalf fun τ => ExpFrame.cj (inc τ) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨fun a b hab => h1 ?_, fun τ τ' e => h2 τ' τ ?_, fun i => ?_⟩
  · have := congrArg ExpFrame.cj hab
    simpa only [cjE_cjE] using this
  · simp only [cjE_cjE] at e
    exact e.symm
  · obtain ⟨τ, hτ | hτ⟩ := h3 i
    · exact ⟨τ, Or.inr (by rw [cjE_cjE]; exact hτ)⟩
    · exact ⟨τ, Or.inl hτ⟩

end GlobalTheory.HalfLabels

namespace GlobalTheory.HalfLabels

theorem exists_aut {E K : Type} [Field E] [NumberField E] [IsGalois ℚ E] [Field K] [CharZero K] (ι i : E →+* K) :
    ∃ σ : E ≃ₐ[ℚ] E, i = ι.comp (σ : E →+* E) := by
  let _ : Algebra E K := ι.toAlgebra
  have : IsScalarTower ℚ E K := IsScalarTower.of_algebraMap_eq fun x => by
    rw [RingHom.algebraMap_toAlgebra, eq_ratCast (algebraMap ℚ K), eq_ratCast (algebraMap ℚ E), map_ratCast]
  let φ : E →ₐ[ℚ] K := i.toRatAlgHom
  refine ⟨AlgEquiv.ofBijective (φ.restrictNormal E) (AlgHom.normal_bijective ℚ E E _), ?_⟩
  ext x
  have h := AlgHom.restrictNormal_commutes φ E x
  exact h.symm

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem isHalf_lab (D : D7) {l : ℕ} [Fact l.Prime] (e0 : D.what₂.LL →+* PadicAlgCl l) : IsHalf (incOf D e0 false) := by
  have : IsGalois ℚ D.host.E := D.host.hostE_isGalois
  set ι : D.host.E →+* PadicAlgCl l := e0.comp D.embE with hι
  have hinc : ∀ τ, incOf D e0 false τ = ι.comp (D.host.sigmaOf (D.eTau τ).1 : D.host.E →+* D.host.E) := fun τ => rfl
  have hcc : ∀ g, ExpFrame.cj (ι.comp (D.host.sigmaOf g : D.host.E →+* D.host.E)) =
      ι.comp (D.host.sigmaOf (g * D.R.cc) : D.host.E →+* D.host.E) := by
    intro g
    have hs : D.host.sigmaOf (g * D.R.cc) = D.host.sigmaOf g * D.host.conj :=
      map_mul (D.host.gal).symm g (D.R.cc)
    ext x
    rw [hs]
    show ι (D.host.sigmaOf g (IsCMField.complexConj D.host.E x)) = ι (D.host.sigmaOf g (D.host.conj x))
    congr 2
    exact Formalism.BasicNotions.bridge_star_holds D.R D.host x
  have hinj : ∀ g g', ι.comp (D.host.sigmaOf g : D.host.E →+* D.host.E) = ι.comp (D.host.sigmaOf g' : D.host.E →+* D.host.E) →
      g = g' := by
    intro g g' h
    have : D.host.sigmaOf g = D.host.sigmaOf g' := AlgEquiv.ext fun x => ι.injective (RingHom.congr_fun h x)
    exact (D.host.gal).symm.injective this
  refine ⟨fun τ τ' h => ?_, fun τ τ' h => ?_, fun i => ?_⟩
  · rw [hinc, hinc] at h
    exact D.eTau.injective (Subtype.ext (hinj _ _ h))
  · rw [hinc, hinc, hcc] at h
    have e := hinj _ _ h
    exact (Formalism.L2.Geo.mem_Psi_iff_mul_cc_notMem _).1 (D.eTau τ).2 (e ▸ (D.eTau τ').2)
  · obtain ⟨σ, hσ⟩ := exists_aut ι i
    have hσg : D.host.sigmaOf (D.host.gal σ) = σ :=
      (D.host.gal).symm_apply_apply σ
    by_cases hg : D.host.gal σ ∈ D.R.Psi
    · refine ⟨D.eTau.symm ⟨_, hg⟩, Or.inl ?_⟩
      rw [hinc, Equiv.apply_symm_apply, hσ, hσg]
    · have hg' : D.host.gal σ * D.R.cc ∈ D.R.Psi := by
        by_contra h'
        exact hg ((Formalism.L2.Geo.mem_Psi_iff_mul_cc_notMem _).2 h')
      refine ⟨D.eTau.symm ⟨_, hg'⟩, Or.inr ?_⟩
      rw [hinc, Equiv.apply_symm_apply, ← hcc, cjE_cjE, hσ, hσg]

theorem halfAt_all (D : D7) (l : ℕ) : HalfAt D l := by
  intro _ e0 b
  cases b
  · exact isHalf_lab D (l := l) e0
  · exact isHalf_cj (isHalf_lab D e0)

end GlobalTheory.HalfLabels

end
end

section

set_option autoImplicit false

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpFrame GlobalTheory.ExpTie GlobalTheory.FrameOf
open scoped TensorProduct

namespace GlobalTheory.FrameOf

theorem finite_classes_of_pres {G Γ : Type} [Group G] [Group Γ] {ι : Γ →* G} {W : Type} [NormedAddCommGroup W]
    [InnerProductSpace ℂ W] {K : Type} [Field K] [NumberField K] [StarRing K] {S : CSD K} {σ : K →+* ℂ}
    {ρ : Γ →* Module.End ℂ W} {J : Subgroup G} {χ : J →* ℂˣ} (P : Bridge.ClassPres ι S σ ρ J χ) :
    ∃ T : Finset G, ∀ g, ∃ γ ∈ ι.range, ∃ s ∈ T, ∃ κ ∈ presJ P, g = γ * s * κ := by
  classical
  have hf : (Set.range P.y).Finite := Set.finite_range _
  refine ⟨hf.toFinset, fun g => ?_⟩
  obtain ⟨c, ⟨γ, k, e⟩, -⟩ := P.reps g
  exact ⟨ι γ, ⟨γ, rfl⟩, P.y c, hf.mem_toFinset.2 ⟨c, rfl⟩, k, k.2, e⟩

theorem classesAt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
    {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz) (j : Fin D.R.m) (t : p.P.T),
    ClassesAt p j t := by
  intro D L hT Gi Gl Kc Y cX ex Csz p j t
  exact finite_classes_of_pres (p.R.B.L j t).pres

end GlobalTheory.FrameOf
end

section

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpFrame GlobalTheory.ExpTie GlobalTheory.FrameOf
open scoped TensorProduct
open Formalism.CohomologicalDescent.LogSmallConstantBounds (Par)

namespace GlobalTheory.FrameOf

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Int

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {l : ℕ} [Fact l.Prime]

theorem norm_ev_intAf_le {i : E →+* PadicAlgCl l} {ev : FiniteAdeleRing (𝓞 F) F ⊗[F] E →+* PadicAlgCl l} (h : EvOk i ev)
    (z : E ⊗[F] FiniteAdeleRing (𝓞 F) F) (hz : z ∈ Formalism.L2.Herm.intAf F E) :
    ‖ev ((Algebra.TensorProduct.comm F (FiniteAdeleRing (𝓞 F) F) E).symm z)‖ ≤ 1 := by
  induction hz using Subring.closure_induction with
  | mem x hx =>
    rcases hx with ⟨⟨_, b, rfl⟩, rfl⟩ | ⟨y, rfl⟩
    · rw [Algebra.TensorProduct.comm_symm_tmul, h.1]
      exact GlobalTheory.AdeleEv.norm_int_le i b
    · rw [Algebra.TensorProduct.comm_symm_tmul]
      exact h.2.1 _ y.2
  | zero => simp
  | one => simp
  | add x y _ _ hx hy => rw [map_add (f := _), map_add (f := _)]; exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hx hy)
  | neg x _ hx => rwa [map_neg, map_neg, norm_neg]
  | mul x y _ _ hx hy => rw [map_mul, map_mul, norm_mul]; exact mul_le_one₀ hx (norm_nonneg _) hy

end Int

end GlobalTheory.FrameOf

namespace GlobalTheory.FrameOf

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Pt

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz)

theorem incOf_mem_range {l : ℕ} [Fact l.Prime] (e0 : D.what₂.LL →+* PadicAlgCl l) (b : Bool) (τ : D.what₂.Tau) (x : D.host.E) :
    incOf D e0 b τ x ∈ Set.range e0 := by
  cases b
  · exact ⟨_, rfl⟩
  · exact ⟨_, rfl⟩

theorem kapAt (j : Fin D.R.m) (P : Par) (w : HeightOneSpectrum (𝓞 D.what₂.LL)) : KapAt p j P w := by
  intro _ e0 b ev rk _ hev
  obtain ⟨y, hy⟩ := exists_levInt p j (p.R.mu w)
  refine ⟨fun _ => 1, fun _ => rfl, fun κ τ a c => ?_⟩
  have hk : kapMat p j (p.R.mu w) ev (fun _ => 1) rk κ τ a c = ev τ (matOf j κ.1 (rk a) (rk c)) := by
    simp [kapMat, Matrix.submatrix_apply, Matrix.map_apply]
  rw [hk]
  refine ⟨?_, ?_⟩
  · refine IntermediateField.adjoin.mono _ _ _ ?_ ((hev τ).2.2.2 _)
    rintro _ ⟨x, rfl⟩
    exact incOf_mem_range e0 b τ x
  · have hz : Formalism.IndefR.Lev.swapAE D (matOf j κ.1 (rk a) (rk c)) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
      rw [← hy κ (rk a) (rk c)]
      exact ((y κ).val (rk a) (rk c)).2
    have h := norm_ev_intAf_le (hev τ) _ hz
    have he : (Algebra.TensorProduct.comm D.host.F (FiniteAdeleRing (𝓞 D.host.F) D.host.F) D.host.E).symm
        (Formalism.IndefR.Lev.swapAE D (matOf j κ.1 (rk a) (rk c))) = matOf j κ.1 (rk a) (rk c) :=
      (Algebra.TensorProduct.comm D.host.F (FiniteAdeleRing (𝓞 D.host.F) D.host.F) D.host.E).symm_apply_apply _
    rwa [he] at h

end Pt

end GlobalTheory.FrameOf
end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpFrame GlobalTheory.ExpTie GlobalTheory.FrameOf
open scoped TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.EvLocal

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem map_eq_zero_of_repr {F A E R ι : Type} [Field F] [CommRing A] [CommRing E] [Algebra F A] [Algebra F E] [CommRing R]
    [Fintype ι] (b : Module.Basis ι F E) (φ : A ⊗[F] E →+* R) (z : A ⊗[F] E)
    (hc : ∀ i, φ (((Algebra.TensorProduct.basis A b).repr z i) ⊗ₜ[F] 1) = 0) : φ z = 0 := by
  have hs : z = ∑ i, ((Algebra.TensorProduct.basis A b).repr z i ⊗ₜ[F] (1 : E)) * ((1 : A) ⊗ₜ[F] b i) := by
    conv_lhs => rw [← (Algebra.TensorProduct.basis A b).sum_repr z]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Algebra.TensorProduct.basis_apply, Algebra.TensorProduct.tmul_mul_tmul, TensorProduct.smul_tmul', smul_eq_mul,
      one_mul]

  rw [hs, map_sum]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [map_mul, hc i, zero_mul]

theorem ev_eq_zero {D : D7} {l : ℕ} [Fact l.Prime] {inc : D.host.E →+* PadicAlgCl l}
    {ev : FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E →+* PadicAlgCl l} (hev : EvOk inc ev)
    (z : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)
    (hz : ∀ w : HeightOneSpectrum (𝓞 D.host.F), ((l : ℕ) : 𝓞 D.host.F) ∈ w.asIdeal → GlobalTheory.HeckeRowsCompare.cmp D w z = 0) :
    ev z = 0 := by
  refine map_eq_zero_of_repr (A := Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) (Module.finBasis D.host.F D.host.E) ev z fun i => ?_
  refine hev.2.2.1 _ fun w hw => ?_
  have e := congrArg (fun z => (Algebra.TensorProduct.basis (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F w)
    (Module.finBasis D.host.F D.host.E)).repr z i) (hz w hw)
  simp only [GlobalTheory.HeckeRowsCompare.cmp, AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at e
  rw [GlobalTheory.HeckeRowsCompare.repr_map, map_zero] at e
  exact e

theorem map_eq_one_of_isLocEnv : ∀ {D : D7} (V : Formalism.BasicNotions.TH.HSp D) {Pl0 : Type} (pl : Pl0 → Pl D.host.E) (ok : Set Pl0) (i : ok × ℕ) (x : Bridge.Gf V) {l : ℕ} [Fact l.Prime] (inc : D.host.E →+* PadicAlgCl l) (ev : FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E →+* PadicAlgCl l), EvOk inc ev → ((l : ℕ) : 𝓞 D.host.E) ∉ (pl i.1.1).asIdeal → isLocEnv V pl ok i x → ((x : GL (Fin V.rank) (FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E)).val).map ev = 1 := by
  intro D V Pl0 pl ok i x l _ inc ev hev hl hx
  have hloc : GlobalTheory.IndefiniteRowSideFullHecke.HeckeIntertwinersInert.LocAt V ((pl i.1).under (𝓞 D.host.F)) x :=
    GlobalTheory.Mem.R3.LiftInertChi.locAt_of_isLocElt V _ x ((GlobalTheory.Hk3Split.isLabElt_of_isTEnv V pl ok i x).2.1 hx)
  ext a b
  have h0 : ev (x.1.1 a b - (1 : Matrix (Fin V.rank) (Fin V.rank) _) a b) = 0 := by
    refine ev_eq_zero hev _ fun w hw => ?_
    have hne : w ≠ (pl i.1).under (𝓞 D.host.F) := by
      rintro rfl
      apply hl
      have h2 : algebraMap (𝓞 D.host.F) (𝓞 D.host.E) (l : 𝓞 D.host.F) ∈ (pl i.1.1).asIdeal := hw
      rwa [map_natCast] at h2
    have h1 : x.1.1.map (GlobalTheory.HeckeRowsCompare.cmp D w) = 1 := hloc w hne
    have h3 := congrFun (congrFun h1 a) b
    rw [Matrix.map_apply] at h3
    rw [map_sub, h3, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  rw [map_sub, sub_eq_zero] at h0
  rw [Matrix.map_apply]
  refine h0.trans ?_
  rw [Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp

end GlobalTheory.EvLocal

end
end

section

open NumberField IsDedekindDomain Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.CovTop Formalism.L2.Pj GlobalTheory.FormTies GlobalTheory.Shares GlobalTheory.ShareOn GlobalTheory.ShareOn.Reading

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.ShareOn.Reading

theorem cast_mem_SS_of_eq {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {X Y : Data E r} (hXY : X = Y)
    (hΨ : X.Ψ = Y.Ψ) {la : Wt Y.Ψ r} {la' : Wt X.Ψ r}
    (hla : ∀ τ (h1 : τ ∈ X.Ψ) (h2 : τ ∈ Y.Ψ) a, la' ⟨τ, h1⟩ a = la ⟨τ, h2⟩ a) {G : Frame Y.Ψ r → ℂ}
    (hG : G ∈ Y.SS la) : (fun x => G (castFrame hΨ x)) ∈ X.SS la' := by
  subst hXY
  have e : la' = la := by funext τ a; exact hla τ.1 τ.2 τ.2 a
  subst e
  exact hG

theorem rdFun_mem_SS : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} {p : PtAt ex Csz} {r : TwoRuns p.T p.P.Gp} (h : RunsOk (fw2 p) r) {i : Fin D.R.m} {C : Type} [MulAction p.P.Gp C] {M : TwoLevels D.host.E D.R.r p.P.Gp C} {ka : Wt M.Ψ D.R.r} {v : HeightOneSpectrum (𝓞 D.what₂.LL)} {e : C ≃ ((r.used v).full.U ((i : ℕ) + 1) (r.used v).full.σ₀).Comp} (ha : ∀ c, (M.comp c).toData = ((r.used v).full.U ((i : ℕ) + 1) (r.used v).full.σ₀).X (e c)) (hb : ∀ c τ (h1 : τ ∈ M.Ψ) (h2 : τ ∈ (((r.used v).full.U ((i : ℕ) + 1) (r.used v).full.σ₀).X (e c)).Ψ) a, ka ⟨τ, h1⟩ a = laR (r.used v).full.toTop ((i : ℕ) + 1) (p.κ i) (e c) ⟨τ, h2⟩ a) (F : (recB (h.laws v).p.toLawsCore).Cusp ((i : ℕ) + 1) (p.κ i)), rdFun (v := v) (e := e) h ha F ∈ M.SS ka := by
  intro D L hT Gi Gl Kc Y cX ex Csz p r h i C _ M ka v e ha hb F c
  have key := GlobalTheory.ReadingTieCheck.reading_mem_SS (h.laws v).p ((i : ℕ) + 1) (p.κ i) F (e c)
  exact cast_mem_SS_of_eq (ha c) ((M.comp_Ψ c).trans (psi_eq ha c)) (fun τ h1 h2 a => hb c τ _ h2 a) key

end GlobalTheory.ShareOn.Reading
end
end
