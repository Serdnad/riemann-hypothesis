module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle046
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LatNotSelfDual
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle674
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle144
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle310
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle687
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsWeilDatumAnisotropicKernelPair
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.Bundle001
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
import Aesop.Main
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceAdeleRing
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicUnitaryTopology
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle366
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralRightTranslate
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LintegralFundamentalDomainLeOfMeetsOrbitsStatement

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle686
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.Bundle002
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLowestKTypeFockMapThetaVectors
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle011
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1830
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
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
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.JointSmooth
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle318
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle469
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle574

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal GlobalTheory.FinPl
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LastRowUnram

theorem chars_unram : Big fun {D} {Γ} _ _ {Pl0 T} {A} {Ks} _ _ _ {R} ch => ∀ (t : T) (v : GlobalTheory.FinPl.Pl D), (∀ w ∈ locPl ch.G t, w.under (𝓞 D.host.F) ≠ v) → ∀ i, i < D.R.m →
    GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.CharUnramAt D (ch.G.chrS (.mu t D.R.m i)) v ∧ GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.CharUnramAt D (ch.G.chrT (.mu t D.R.m i)) v := by
  refine ⟨0, fun ε CF _ => ⟨0, fun D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F hS ch _ _ => ?_⟩⟩
  intro t v hv i hi
  classical
  have hL : R.toLevCh.Is A.μ0 := hS.core.lev
  have hS0 := GlobalTheory.RowVacScalar.notMem_S0_of_no_place_above ch.G t hv
  have hQ : ∀ PP ∈ R.toLevCh.Q t, PP ∈ locPl ch.G t := fun PP h => by
    unfold locPl
    exact Finset.mem_union_right _ h
  have hmu : GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.CharUnramAt D (R.toLevCh.mu t (i + 1)) v := by
    refine GlobalTheory.SeeSaw.LevelTest.charUnramAt_of fun w hw => ?_
    show GlobalTheory.LFun.UnrAt (R.toLevCh.mu0 (i + 1) * R.toLevCh.xi t) w
    refine GlobalTheory.LFun.UnrAt.mul ?_ ?_
    · refine (GlobalTheory.LFun.unrAt_iff_of_chrEq (hL.mu0 ⟨i, hi⟩) w).2 ((R.toLevCh.C.isMu0 ⟨i, hi⟩).unr w fun k hk => ?_)
      refine hS0 (ch.G.pl.mem_S0_of_sum_eq.2 (Or.inr ((GlobalTheory.ChiGrid.S1_mem_OmF D).2 ?_)))
      have : ((D.host.g k : ℕ) : 𝓞 D.host.F) ∈ (w.under (𝓞 D.host.F)).asIdeal := by
        show algebraMap _ (𝓞 D.host.E) _ ∈ w.asIdeal
        rw [map_natCast]; exact hk
      rw [hw] at this
      fin_cases k
      · exact Or.inl this
      · exact Or.inr (Or.inl this)
    · refine (GlobalTheory.LFun.unrAt_iff_of_chrEq (hL.xi t) w).2 ?_
      by_contra hu
      rcases (hL.Q_ram t w).1 hu with h | ⟨P', hP', hc⟩
      · exact hv w (hQ w h) hw
      · exact hv P' (hQ P' hP') ((GlobalTheory.LevelPlaces.under_eq_of_isConjPl hc).trans hw)
  have key := GlobalTheory.RowVacScalar.attChr_charUnramAt hmu (GlobalTheory.RowVacScalar.eta_charUnramAt hL v)
  exact ⟨key _, key _⟩

end GlobalTheory.LastRowUnram
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.LocAsm
open GlobalTheory.SplitFlip

section General
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem moved_pureTensor_eq_mul (G : Grid k) (keep : Bool) (g : G.VertexGroup)
    (hg : ∀ i < G.m, g (i, G.m) = 1 ∧ g (i + 1, G.m) = 1)
    (φ : ∀ b : Edge, Matrix (Fin (G.rank b.tgt)) (Fin (G.rank b.src)) k → ℂ) (z : G.Args) :
    moved G keep g (G.lines₂ (oppositePath G.m) φ) z =
      moved G keep g (G.lines₂ (oppositePath G.m) (exOne φ)) z *
        ∏ i ∈ Finset.range G.m, φ (.ex i G.m) (z (.ex i G.m)) := by
  have h1 : ((List.range G.m).map fun i => φ (.ex i G.m) (G.moveArgs .one g z (.ex i G.m))) =
      (List.range G.m).map fun i => φ (.ex i G.m) (z (.ex i G.m)) := by
    refine List.map_congr_left fun i hi => ?_
    obtain ⟨ha, hb⟩ := hg i (List.mem_range.1 hi)
    simp only [Grid.moveArgs, Edge.src, Edge.tgt, ha, hb, map_one, inv_one, Units.val_one, Matrix.one_mul,
      Matrix.mul_one]
  have h2 : ((List.range G.m).map fun i => exOne φ (.ex i G.m) (G.moveArgs .one g z (.ex i G.m))).prod = 1 := by
    simp [exOne]
  simp only [moved, Grid.pathAct, Grid.lines₂, oppositePath, List.map_append, List.prod_append, List.map_map,
    Function.comp_def]
  rw [h1, h2]
  show _ = _ * ((List.range G.m).map fun i => φ (.ex i G.m) (z (.ex i G.m))).prod
  simp only [exOne_theta, List.map_reverse]
  ring

theorem moved_exOne_fill (G : Grid k) (hs : 1 ≤ G.s) (keep : Bool) (g : G.VertexGroup) (γ : List Edge)
    (φ : ∀ b : Edge, Matrix (Fin (G.rank b.tgt)) (Fin (G.rank b.src)) k → ℂ) (x : ColArgs G) (y y' : RowArgs G)
    (e : Vars G) :
    moved G keep g (G.lines₂ γ (exOne φ)) (fill hs x y e) =
      moved G keep g (G.lines₂ γ (exOne φ)) (fill hs x y' e) := by
  simp only [moved, Grid.pathAct, Grid.lines₂]
  congr 3
  refine List.map_congr_left fun b _ => ?_
  cases b <;> rfl

variable [MeasurableSpace k] [BorelSpace k]

theorem flatTensor_moved_pureTensor (G : Grid k) (hs : 1 ≤ G.s) (ψ : AddChar k Circle) (ν : Measure k) (keep : Bool)
    (g : G.VertexGroup) (hg : ∀ i < G.m, g (i, G.m) = 1 ∧ g (i + 1, G.m) = 1)
    (φ : ∀ b : Edge, Matrix (Fin (G.rank b.tgt)) (Fin (G.rank b.src)) k → ℂ) (x : ColArgs G) (y : RowArgs G) :
    flatTensor hs ψ ν (moved G keep g (G.lines₂ (oppositePath G.m) φ)) x y =
      flatTensor hs ψ ν (moved G keep g (G.lines₂ (oppositePath G.m) (exOne φ))) x 0 *
        ∏ i ∈ Finset.range G.m, φ (.ex i G.m) (y i)ᵀ := by
  unfold flatTensor flatIntegrand
  rw [← integral_mul_const]
  congr 1
  funext e
  rw [moved_pureTensor_eq_mul G keep g hg φ, moved_exOne_fill G hs keep g _ φ x y 0 e]
  simp only [fill_ex]
  ring

end General

theorem Reps.elt_row {k : Type} [Field k] {G : Grid k} {hs : 1 ≤ G.s} {J : G.Level} (ρ : Reps hs J)
    (β : Cosets hs J) : ∀ i < G.m, ρ.elt β (i, G.m) = 1 ∧ ρ.elt β (i + 1, G.m) = 1 := by
  intro i hi
  refine ⟨dif_neg (by simp only; omega), ?_⟩
  by_cases h : i + 1 = G.m
  · have key : ∀ j (hj : j = i + 1), ρ.elt β (G.m, j) = 1 := by
      intro j hj
      subst hj
      rw [Reps.elt, onColumn_apply]
      exact dif_neg (by omega)
    rw [h]
    exact key G.m h.symm
  · exact dif_neg (by simp only; omega)

theorem flatTensor_rowFactor : Big fun {D} _ _ _ _ {T} _ _ _ _ _ _ ch => ∀ (t : T) (β : CosFam ch.G t) (w : locPl ch.G t) (φ : ∀ b : GlobalTheory.SplitFlip.Edge, Matrix (Fin ((locGrid ch.G t w.1).rank b.tgt)) (Fin ((locGrid ch.G t w.1).rank b.src)) (Kw w.1) → ℂ), (∀ b ∈ GlobalTheory.SplitFlip.oppositePath D.R.m, GlobalTheory.SplitFlip.IsNatDatum (unifAt w.1) (depthAt ch.G w.1) (φ b)) → ∀ (u : ∀ j : Fin D.R.m, WO (ch.G.V (.top j)) (ch.G.V (.top (j + 1)))) (y : ∀ i : Fin D.R.m, WO (ch.G.pS (.chi i D.R.m : Pair T)) (ch.G.pT (.chi i D.R.m : Pair T))), flatTensor one_le_sLen (psiAt ch.W w.1) (unitVol w.1) (moved (locGrid ch.G t w.1) (keepAt ch.G w.1) ((repsAt ch.G t w.1).elt (β w)) ((locGrid ch.G t w.1).lines₂ (GlobalTheory.SplitFlip.oppositePath D.R.m) φ)) (ch.S.colAt t w.1 u) (ch.S.rowAt t w.1 y) = flatTensor one_le_sLen (psiAt ch.W w.1) (unitVol w.1) (moved (locGrid ch.G t w.1) (keepAt ch.G w.1) ((repsAt ch.G t w.1).elt (β w)) ((locGrid ch.G t w.1).lines₂ (GlobalTheory.SplitFlip.oppositePath D.R.m) (GlobalTheory.LocAsm.exOne φ))) (ch.S.colAt t w.1 u) 0 * ∏ i : Fin D.R.m, φ (.ex i D.R.m) (ch.S.B.coord t w.1 (X := (i, D.R.m)) (Y := (i + 1, D.R.m)) ⟨i.2.le, le_rfl⟩ ⟨i.2, le_rfl⟩ ((y i).map fun a => cpt w.1 (toEAf D a))) := by
  refine ⟨0, fun _ _ _ => ⟨0, ?_⟩⟩
  intro D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F _ ch _ _ t β w φ _ u y
  refine (flatTensor_moved_pureTensor (locGrid ch.G t w.1) one_le_sLen _ _ _ _ (Reps.elt_row _ _) φ _ _).trans ?_
  congr 1
  rw [Finset.prod_range]
  refine Finset.prod_congr rfl fun i _ => ?_
  simp only [GridChoice.rowAt]
  rw [dite_eq_left (show (i : ℕ) < D.R.m from i.2)]
  rfl

end GlobalTheory.LocAsm
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

theorem _root_.GlobalTheory.T.expansion_product_invariant_inner_vertex_level : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) {t : T}
    {Φ : G.Datum} {β : CosFam G t} {τ : PureDat G t →₀ ℂ} {μ₀ : T},
    L.Is μ₀ → (Nat.Coprime D.host.pde (D.host.QS * D.host.q) ∧ Nat.Coprime D.host.pde' (D.host.QS * D.host.q)) → (∀ P ∈ L.Q t, ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal) → t ∈ U → β ∈ S.supp t Φ → S.IsExpansion t Φ β τ →
    (∀ d ∈ τ.support, (∀ j, S.Z.HasVec (d.1 j)) ∧ ∀ i, S.Z.HasVec (d.2 i)) →
    ∀ (j : ℕ) (hj : j + 1 < D.R.m) (k : FinPt G (.top (j + 1))), finG (G.V (.top (j + 1))) k ∈ S.levTop t Φ β (j + 1) hj →
    ∀ (w : ∀ j' : Fin D.R.m, WO (G.pS (.top t j' : Pair T)) (G.pT (.top t j' : Pair T)))
      (z : ∀ i : Fin D.R.m, WO (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T))),
      (τ.sum fun d a => a * (∏ j', movedCol S d j hj ((S.N.u (.top (j + 1)))⁻¹ * k * S.N.u (.top (j + 1))) j' (w j')) *
          ∏ i, S.Z.vec (d.2 i) (z i)) =
        τ.sum fun d a => a * (∏ j', S.Z.vec (d.1 j') (w j')) * ∏ i, S.Z.vec (d.2 i) (z i) := by
  first | exact @GlobalTheory.ExpansionInvariance.product_invariant | exact GlobalTheory.ExpansionInvariance.product_invariant | (intros; apply GlobalTheory.ExpansionInvariance.product_invariant <;> assumption)
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR Formalism.IndefR.Links Formalism.L2.DIV GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RowChain

theorem bplus_eq_per {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (Wl : G.Weil) (t : T)
    (M : GlobalTheory.FunObj.Vol G) (hM : M.Is t) (φ : Fn G (.top 0)) (F : Fn G (.grid D.R.m 0)) :
    Bplus Wl M φ F = (topLev G hM).per Wl.ψ φ F :=
  GlobalTheory.T.besselPeriodCorankOneLess_eq_topBesselLevel_period G Wl t M hM φ F

end GlobalTheory.RowChain

end
end

section

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm

namespace GlobalTheory.WeilConv

theorem weilConvergence_of_siegelSet (hRT : GlobalTheory.Published.SiegelSetUnitary) : GlobalTheory.SquareSt.WeilConvergence := by
  intro D ψ θ hθ ε M X χ χ' ω hω p hsig hd ν 𝓕 hν Φ hΦ
  obtain ⟨τ, hτ⟩ := hsig
  obtain ⟨i1, i2, i3, i4, i5, i6, i7⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D M
  have hν1 := hν.1
  obtain ⟨r, Xf, Yf, hW⟩ := GlobalTheory.SiegelSet.exists_isWittFrame (GlobalTheory.AdelicU.isCMExt_host D) (isHermND_gram M)
  have hr : r ≤ p := GlobalTheory.T.hermitianWittIndex_le_negative_signature M hτ hW
  obtain ⟨K, Ω, c, hK, hΩ, -, hc, -, hcl, hcov, ⟨C₀, hC₀, hconj⟩, hmeas, -, -⟩ :=
    hRT D.host.F D.host.E D.sp.cm.sig (GlobalTheory.AdelicU.isCMExt_host D) M.rank M.gram (isHermND_gram M) r Xf Yf hW
  obtain ⟨-, C₁, hC₁⟩ := hmeas ν hν1
  obtain ⟨N, C, hC⟩ := GlobalTheory.T.thetaKernel_siegelSet_le_torusPower_height ψ θ hθ ε M X χ χ' ω hω Φ hΦ r Xf Yf hW Ω C₀ K c hΩ hC₀ hK hc hconj
  have hω' : IsWeilDatumO ψ (sgn ε M) X χ χ' (ω.toSgn ε) := hω
  have hcont : ∀ h, Continuous fun g => thetaKO ω g h Φ := fun h =>
    (hω'.om_cont Φ hΦ 0).comp ((continuous_ofSgn_symm ε M).prodMk continuous_const)
  have hinv : ∀ h, ∀ γ ∈ GQ M, ∀ g, thetaKO ω (γ * g) h Φ = thetaKO ω g h Φ := fun h γ hγ g => by
    have e1 : (((ofSgn ε M).symm (γ * g), h) : GA D (sgn ε M) × GA D X) =
        ((ofSgn ε M).symm γ, 1) * ((ofSgn ε M).symm g, h) := by simp
    show (ω.toSgn ε) ((ofSgn ε M).symm (γ * g), h) Φ 0 = (ω.toSgn ε) ((ofSgn ε M).symm g, h) Φ 0
    rw [e1, map_mul, Module.End.mul_apply]
    exact hω'.om_aut _ (ofSgn_symm_mem_GQ ε hγ) 1 (one_mem _) _ (hω'.om_pres _ _ hΦ)
  set S := GlobalTheory.SiegelSet.siegelSet D.sp.cm.sig M.gram Xf Yf Ω c K with hSdef
  have hSm : MeasurableSet S := hcl.measurableSet
  have hScov : ∀ g, ∃ γ ∈ GQ M, γ * g ∈ S := fun g => by
    obtain ⟨γ, hγ, s, hs, e⟩ := hcov g
    refine ⟨γ⁻¹, inv_mem hγ, ?_⟩
    rw [e, inv_mul_cancel_left]
    exact hs
  have hI := GlobalTheory.T.lintegral_siegelCone_inv_modulus_lt_top_weil D.host.F M.rank r X.rank hc (by omega)
  set I := ∫⁻ t in GlobalTheory.SiegelSet.cone r c, ENNReal.ofReal (∏ i, t i ^ (Module.finrank ℚ D.host.F * X.rank)) *
      ENNReal.ofReal ((GlobalTheory.SiegelSet.modulus D.host.F M.rank t * ∏ i, t i)⁻¹) with hIdef
  have key : ∀ h, ∫⁻ g in 𝓕, ‖thetaKO ω g h Φ‖ₑ ∂ν ≤
      C₁ * (ENNReal.ofReal (max C 0 * (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.height θ X h : ℝ) ^ N) * I) := fun h => by
    have hA : 0 ≤ max C 0 * (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.height θ X h : ℝ) ^ N := by positivity
    calc ∫⁻ g in 𝓕, ‖thetaKO ω g h Φ‖ₑ ∂ν ≤ ∫⁻ g in S, ‖thetaKO ω g h Φ‖ₑ ∂ν :=
          GlobalTheory.T.lintegral_fundamentalDomain_le_of_meets_all_orbits (GQ M) ν hν.2 hSm hScov (hcont h).enorm.measurable
            (fun γ hγ g => by rw [hinv h γ hγ g])
      _ ≤ C₁ * ∫⁻ t in GlobalTheory.SiegelSet.cone r c, ENNReal.ofReal (max C 0 * (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.height θ X h : ℝ) ^ N *
            ∏ i, t i ^ (Module.finrank ℚ D.host.F * X.rank)) *
            ENNReal.ofReal ((GlobalTheory.SiegelSet.modulus D.host.F M.rank t * ∏ i, t i)⁻¹) := by
          refine hC₁ (fun g => ‖thetaKO ω g h Φ‖ₑ) _ (by fun_prop) fun q hq t ht a ha k hk => ?_
          have ht0 : ∀ i, 0 < t i := ht.1
          have hP : 0 ≤ ∏ i, t i ^ (Module.finrank ℚ D.host.F * X.rank) :=
            Finset.prod_nonneg fun i _ => pow_nonneg (ht0 i).le _
          rw [← ofReal_norm_eq_enorm]
          refine ENNReal.ofReal_le_ofReal ((hC h q hq t ht a ha k hk).trans ?_)
          have hH : 0 ≤ (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.height θ X h : ℝ) ^ N := by positivity
          gcongr
          exact le_max_left _ _
      _ = C₁ * (ENNReal.ofReal (max C 0 * (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.height θ X h : ℝ) ^ N) * I) := by
          rw [hIdef, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
          congr 1
          exact lintegral_congr fun t => by rw [ENNReal.ofReal_mul hA, mul_assoc]
  refine ⟨N, (C₁ : ℝ) * max C 0 * I.toReal, fun h => ⟨⟨(hcont h).aestronglyMeasurable, ?_⟩, ?_⟩⟩
  · exact (key h).trans_lt (by finiteness)
  · rw [integral_norm_eq_lintegral_enorm (hcont h).aestronglyMeasurable]
    have hA : 0 ≤ max C 0 * (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.height θ X h : ℝ) ^ N := by positivity
    refine (ENNReal.toReal_mono (by finiteness) (key h)).trans (le_of_eq ?_)
    rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal hA, ENNReal.coe_toReal]
    ring

end GlobalTheory.WeilConv

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FlipRowTheta

theorem row_isThetaFunO : Big fun ch => ∀ t Φ τ, IsFlipFin t ch.S.B ch.rm Φ τ → ∀ d ∈ τ.support, ∀ i,
    IsThetaFunO ch.W.ψ _ _ (d.1 i) := by
  refine ⟨0, fun ε CF _ => ⟨0, fun D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F hSet ch hch hsc => ?_⟩⟩
  intro t Φ τ hτ d hd i
  obtain ⟨e, _he, φ, hφ, _⟩ := hτ
  exact GlobalTheory.JointHarm.isThetaFunO_of_isThetaAt ch.W.ψ_std ch.W.θ_is
    ((hφ d hd).1 i).2 (ch.rm.vX_is i D.R.m i.2 le_rfl).2.theta

end GlobalTheory.FlipRowTheta

end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped NNReal
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.LastLevUnit

open GlobalTheory.FunObj.UnfModel GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.RootEx ValuativeRel

section Loc
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem symPr_of_eq_zero {n : Type*} [Fintype n] [DecidableEq n] {c : ℕ} (hc : c = 0) (C : Subgroup (GL (n ⊕ Fin c) k)) :
    symPr C = C.comap (embX c) := by
  subst hc; exact symPr_zero C

theorem embX_frame_int {a c b : ℕ} (h : a + c = b) (z : GL (Fin a) k) :
    (∀ i j : Fin b, (embX c z).val ((frame h).symm i) ((frame h).symm j) ∈ 𝒪[k]) ↔ ∀ i j, z.val i j ∈ 𝒪[k] := by
  constructor
  · intro H i j
    have := H (frame h (.inl i)) (frame h (.inl j))
    simpa [embX] using this
  · intro H i j
    generalize (frame h).symm i = r
    generalize (frame h).symm j = s
    rcases r with r | r <;> rcases s with s | s <;> simp only [embX, Units.coe_map, MonoidHom.coe_mk, OneHom.coe_mk,
      fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁, fromBlocks_apply₂₂]
    · exact H r s
    · exact zero_mem _
    · exact zero_mem _
    · rw [Matrix.one_apply]; split_ifs
      · exact one_mem _
      · exact zero_mem _

theorem embX_mem_frame_KO {a c b : ℕ} (h : a + c = b) (x : GL (Fin a) k) :
    embX c x ∈ (KO k (Fin b)).map (frameGL (k := k) h).toMonoidHom ↔ x ∈ KO k (Fin a) := by
  rw [Subgroup.map_equiv_eq_comap_symm', Subgroup.mem_comap, mem_KO_iff, mem_KO_iff, ← map_inv, ← map_inv]
  exact and_congr (embX_frame_int h x) (embX_frame_int h x⁻¹)

theorem symPr_conjLevel_last {Γ : Grid k} (hs : 1 ≤ Γ.s) (J : Γ.Level) (g : Γ.VertexGroup) {j : ℕ} (hj : j < Γ.m)
    (hlast : j + 1 = Γ.m) (hJ : J (Γ.m, j) = KO k _) (hg : g (Γ.m, j) = 1) :
    symPr (conjLevel hs J g hj) = KO k (Fin (topRank Γ j)) := by
  rw [symPr_of_eq_zero (by omega), conjLevel, hJ, hg]
  ext x
  rw [Subgroup.mem_comap, map_one]
  have e : Subgroup.map (MulEquiv.toMonoidHom (1 : MulAut (GL (Fin (Γ.rank (Γ.m, j))) k))) (KO k (Fin (Γ.rank (Γ.m, j)))) =
      KO k _ := Subgroup.map_id _
  rw [e]
  exact embX_mem_frame_KO _ x

end Loc
end GlobalTheory.LastLevUnit

namespace GlobalTheory.LastLevUnit

open GlobalTheory.FunObj.UnfModel GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.RootEx ValuativeRel GlobalTheory.FunObj.LevRowSucc

theorem elt_last {k : Type*} [Field k] {Γ : Grid k} {hs : 1 ≤ Γ.s} {J : Γ.Level} (ρ : Reps hs J) (β : Cosets hs J) {j : ℕ}
    (hj : j + 2 = Γ.m) : ρ.elt β (Γ.m, j + 1) = 1 := by
  rw [Reps.elt, onColumn_apply]
  dsimp only
  rw [dite_eq_right (by omega)]

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts}

theorem givenLevel_pos (G : GridData L sc) (t : T) (w : Pl D.host.E) :
    ∀ X : ℕ × ℕ, X.1 ≠ 0 → X.2 ≠ 0 → givenLevel G t w X = KO (Kw w) (Fin ((locGrid G t w).rank X))
  | (0, _), h, _ => absurd rfl h
  | (_ + 1, 0), _, h => absurd rfl h
  | (_ + 1, _ + 1), _, _ => rfl

theorem levTop_last_inf_UA {G : GridData L sc} (W : G.Weil) {U : Set T} (S : GridChoice W U) (t : T) (Φ : G.Datum)
    (β : CosFam G t) (j : ℕ) (h : j + 1 < D.R.m) (hj : j + 2 = D.R.m) :
    S.levTop t Φ β (j + 1) h ⊓ UA D.sp.cm (G.V (.top (j + 1))).gram = G.levMax (.top (j + 1)) := by
  rw [GridData.levMax]
  exact prodLev_inf_UA (S.βp_is (j + 1) h.le) (G.isV (X := .top (j + 1)) h.le fun _ e => by cases e).sd (locPl G t) _ _
    fun w => symPr_conjLevel_last one_le_sLen (givenLevel G t w.1) ((repsAt G t w.1).elt (β w)) h (by show j + 1 + 1 = D.R.m; omega)
      (givenLevel_pos G t w.1 _ (by show D.R.m ≠ 0; omega) (by show j + 1 ≠ 0; omega)) (elt_last _ _ hj)

theorem levTop_inf_UA_levJ {G : GridData L sc} (W : G.Weil) {U : Set T} (S : GridChoice W U) (t : T) (Φ : G.Datum)
    (β : CosFam G t) : ∀ n (h : n < D.R.m), n + 1 = D.R.m → 2 ≤ D.R.m →
    S.levTop t Φ β n h ⊓ UA D.sp.cm (G.V (.top n)).gram = levJ G t (.top n)
  | 0, _, h1, h2 => absurd h1 (by omega)
  | j + 1, h, h1, _ => levTop_last_inf_UA W S t Φ β j h (by omega)

theorem levTop_iff_levJ : Big fun {D} _ _ _ _ _ _ _ _ _ _ _ ch => ∀ t Φ β (h : D.R.m - 1 < D.R.m), 2 ≤ D.R.m → ∀ (k : FinPt ch.G (.top (D.R.m - 1))),
    finG (ch.G.V (.top (D.R.m - 1))) k ∈ ch.S.toGridChoice.levTop t Φ β (D.R.m - 1) h ↔
      finG (ch.G.V (.top (D.R.m - 1))) k ∈ levJ ch.G t (.top (D.R.m - 1)) :=
  ⟨0, fun _ _ _ => ⟨0, fun D _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ s ch _ _ t Φ β h hm k => by
    have hU : finG (ch.G.V (.top (D.R.m - 1))) k ∈ UA D.sp.cm (ch.G.V (.top (D.R.m - 1))).gram := GlobalTheory.LevSplit.finE_mem_UA _ _
    rw [← levTop_inf_UA_levJ ch.W ch.S.toGridChoice t Φ β (D.R.m - 1) h (by omega) hm]
    exact ⟨fun h' => ⟨h', hU⟩, fun h' => h'.1⟩⟩⟩

end GlobalTheory.LastLevUnit
end
end
