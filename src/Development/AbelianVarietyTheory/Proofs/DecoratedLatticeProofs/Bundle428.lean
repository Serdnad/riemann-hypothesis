module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FrameTopAlt
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle385
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsFinCombSingleZero
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle414
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasInfExpOfOrder
public import Formalism.LocalRingCardinality.Bundle009
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle350
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle376
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle379
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle344
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.FlatSpaceComponents
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle163
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle404
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle378
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle165
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle188
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle143
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle272
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2107
import Development.AbelianVarietyTheory.Proofs.HeightProofs.EmbeddingXiZeroNeZero
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle317
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle274
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsLevMeas
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle406
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsOneComb
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsOpenKerUnramMulTame
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiStarOfMid
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MidChart

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Fam.CommIs

open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.PairLift GlobalTheory.Chain.RealIt GlobalTheory.Core.Mi

theorem isKFin_of_mem {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (τ : D.what₂.Tau) {x : M.H τ}
    (hx : x ∈ GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.kfin M τ) : Formalism.MainNotions.S.IsKFin (M.ε τ) (M.σ τ) x := by
  induction hx using Submodule.span_induction with
  | mem x h => exact h
  | zero => exact ⟨⊥, inferInstance, Submodule.zero_mem _, fun g _ v hv => by
      rw [(Submodule.mem_bot _).1 hv, map_zero]; exact Submodule.zero_mem _⟩
  | add x y _ _ hx hy =>
    obtain ⟨S₁, h1, h2, h3⟩ := hx
    obtain ⟨S₂, k1, k2, k3⟩ := hy
    refine ⟨S₁ ⊔ S₂, inferInstance, Submodule.add_mem_sup h2 k2, fun g hg v hv => ?_⟩
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hv
    rw [map_add (f := _)]
    exact Submodule.add_mem_sup (h3 g hg a ha) (k3 g hg b hb)
  | smul c x _ hx =>
    obtain ⟨S₁, h1, h2, h3⟩ := hx
    exact ⟨S₁, h1, S₁.smul_mem c h2, h3⟩

theorem itSpans_of (hDS : GlobalTheory.Published.DiscreteSeriesCover) (hHC : GlobalTheory.Published.HarishChandraModules) {D : D7} {V W : HSp D}
    {S S' : D.what₂.Tau → SPar} (M : DSModel V S) (M' : DSModel W S') (θ : InfFam D) (ψ : AddChar (AF D.host.F) ℂ)
    (aS aT : D.what₂.Tau → ℚ) (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (f : WO V W → ℂ)
    (It : PolF D W.rank V.rank →ₗ[ℂ] SmT M' →ₗ[ℂ] SmT M) (hθ : IsInfFam θ) (hw : IsWeilExp ψ V W aS aT ω)
    (hv : IsVacVec ψ θ M M' f) (hi : IsItW θ M M' ω (ptOf ψ θ M M' f) It) : GlobalTheory.Core.Mi.ItSpans M M' It := by
  have hle := GlobalTheory.ItOnto.kfinSpan_le_span_it hDS hHC D V W S S' M M' θ ψ aS aT ω f It hθ hw hv hi
  intro v hv
  have hv' := hle (Submodule.subset_span ⟨v, fun τ => Submodule.subset_span (hv τ), rfl⟩)
  refine (Submodule.span_le.2 ?_) hv'
  rintro w ⟨P, u, hu, rfl⟩
  have hu' : u ∈ Submodule.comap (It P) (Submodule.span ℂ
      {x | ∃ (P : PolF D W.rank V.rank) (y : M'.Vec), GlobalTheory.Core.Mi.KVecP M' y ∧ x = It P (PiTensorProduct.tprod ℂ y)}) := by
    refine (Submodule.span_le.2 ?_) hu
    rintro _ ⟨y, hy, rfl⟩
    exact Submodule.subset_span ⟨P, y, fun τ => isKFin_of_mem _ _ (hy τ), rfl⟩
  exact hu'

end GlobalTheory.Fam.CommIs


open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.PairLift GlobalTheory.Chain.RealIt in
theorem GlobalTheory.Fam.commOf_is : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex) (u : D.what₂.Word), PkHyp W → ∀ g : GlobalTheory.Fam.Geo D, GeoMeas (pk W) g → (∀ j, j ≤ D.R.m → (g.x j).Is) → (commOf (pk W) u g).Is := by
  intro hDS hHC D L hT Gi Gl Kc Yd cX ex W u hp g hm hx
  have hC : W.Q.Rl.Char3 W.Q.F := hp.bot.hyp.2.2.2.1
  have hS : StepsOK (pk W) := GlobalTheory.Chain.StepVac.stepsOK _ _ _ _ _ _ (pk W) hC.lev hC.models.inf hC.chain.ωY hC.chain.ωX
    hC.chain.vY hC.chain.vX
  have hθ : IsInfFam (pk W).θ := hC.models.inf
  have hm1 : D.R.m - 1 < D.R.m := Nat.sub_lt (lt_of_lt_of_le two_pos D.R.two_le_m) one_pos
  have hY : ∀ j, j + 1 < D.R.m → GlobalTheory.Core.Mi.ItSpans ((pk W).MY j) ((pk W).MY (j + 1)) ((pk W).ItY j) := by
    intro j hj
    have h := hS.1 W.P.A3.A.μ0 ⟨j, by omega⟩ hj
    obtain ⟨χS, χT, hω, he⟩ := h.1
    exact GlobalTheory.Fam.CommIs.itSpans_of hDS hHC _ _ _ _ _ _ _ _ _ hθ ⟨χS, χT, hω, he⟩ h.2 (hC.chain.ItY W.P.A3.A.μ0 j hj)
  have hX : GlobalTheory.Core.Mi.ItSpans ((pk W).MY (D.R.m - 1)) (pk W).MX (pk W).ItX := by
    have h := hS.2 W.P.A3.A.μ0 ⟨D.R.m - 1, hm1⟩ rfl
    obtain ⟨χS, χT, hω, he⟩ := h.1
    exact GlobalTheory.Fam.CommIs.itSpans_of hDS hHC _ _ _ _ _ _ _ _ _ hθ ⟨χS, χT, hω, he⟩ h.2 (hC.chain.ItX W.P.A3.A.μ0)
  have hXc : ∀ n (e : D.R.m - 1 = n), GlobalTheory.Core.Mi.ItSpans ((pk W).MY n) (pk W).MX
      (Eq.rec (motive := fun n _ => PolF D D.sp.X'.rank (Yc D n).rank →ₗ[ℂ] SmT (pk W).MX →ₗ[ℂ] SmT ((pk W).MY n))
        (pk W).ItX e) := by
    intro n e
    subst e
    exact hX
  refine ⟨W.Q.stdChar, hθ, hx, GlobalTheory.SeeSaw.Inh.coCpt_of_isDefinite D.sp.X'_sig fun τ => Or.inl (D.X'_posDef τ), hm.μf, hm.ρJ,
    hm.ρB, fun j hj => hY j hj, fun j h => hXc (j + 1) (idx_top h)⟩
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.SeeSaw GlobalTheory.LocMod
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.IndicatorVac

theorem splitC (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (q : GlobalTheory.FinPl.SplitPt D k) : IsSplitIdem D (cA D q.e) := by
  obtain ⟨h1, h2, v, ε, hv, h3⟩ := q.split
  refine ⟨by rw [← map_mul, h1], ?_, v, ε, hv, ?_⟩
  · rw [GlobalTheory.LatVac.cA_cA, mul_comm, h2]
  · rw [GlobalTheory.LatVac.cA_cA, add_comm, h3]

theorem e_eq (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (q : GlobalTheory.FinPl.SplitPt D k) : q.sec 1 = q.e := by
  have := q.sec_pr 1; rw [map_one, mul_one] at this; exact this

theorem mul_e (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (q : GlobalTheory.FinPl.SplitPt D k) (e' : Formalism.L2.Theta.AE D) (he : e' * e' = e') : q.e * e' = 0 ∨ q.e * e' = q.e := by
  have hp : q.pr e' * q.pr e' = q.pr e' := by rw [← map_mul, he]
  rcases (IsIdempotentElem.iff_eq_zero_or_one.1 hp) with h | h
  · left; rw [← q.sec_pr, h, map_zero]
  · right; rw [← q.sec_pr, h, e_eq]


theorem cases (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (q : GlobalTheory.FinPl.SplitPt D k) (e' : Formalism.L2.Theta.AE D) (he' : IsSplitIdem D e') {m n : ℕ} (u : Mx D m n)
    (hsupp : ∀ i j, (q.e + cA D q.e) * u i j = u i j) (hu : IsHalf e' u) :
    u = 0 ∨ IsHalf q.e u ∨ IsHalf (cA D q.e) u := by
  obtain ⟨h1, h2, -⟩ := he'
  have hc1 : cA D e' * cA D e' = cA D e' := by rw [← map_mul, h1]
  have hA := mul_e D k q e' h1
  have hB : cA D q.e * e' = 0 ∨ cA D q.e * e' = cA D q.e := by
    rcases mul_e D k q (cA D e') hc1 with h | h
    · left; have := congrArg (cA D) h; rwa [map_mul, GlobalTheory.LatVac.cA_cA, map_zero] at this
    · right; have := congrArg (cA D) h; rwa [map_mul, GlobalTheory.LatVac.cA_cA] at this
  have hu' : ∀ i j, u i j = q.e * e' * u i j + cA D q.e * e' * u i j := fun i j => by
    rw [mul_assoc, mul_assoc, hu i j, ← add_mul, hsupp i j]
  have hee : q.e * q.e = q.e := q.split.1
  have hce : cA D q.e * cA D q.e = cA D q.e := by rw [← map_mul, hee]
  rcases hA with hA | hA <;> rcases hB with hB | hB
  · left; ext i j; rw [hu' i j, hA, hB]; simp
  · right; right; intro i j; rw [hu' i j, hA, hB, zero_mul, zero_add, ← mul_assoc, hce]
  · right; left; intro i j; rw [hu' i j, hA, hB, zero_mul, add_zero, ← mul_assoc, hee]
  · exfalso
    have hpe : q.pr q.e = 1 := by rw [← e_eq D k q, q.pr_sec]
    have h7 : q.e = 0 := by
      rcases mul_e D k q (cA D e') hc1 with h | h
      · have h5 : cA D q.e * e' = 0 := by
          have := congrArg (cA D) h; rwa [map_mul, GlobalTheory.LatVac.cA_cA, map_zero] at this
        have h6 : cA D q.e = 0 := hB.symm.trans h5
        have := congrArg (cA D) h6; rwa [GlobalTheory.LatVac.cA_cA, map_zero] at this
      · calc q.e = q.e * cA D e' := h.symm
          _ = q.e * e' * cA D e' := by rw [hA]
          _ = 0 := by rw [mul_assoc, h2, mul_zero]
    rw [h7, map_zero] at hpe
    exact zero_ne_one hpe

end GlobalTheory.IndicatorVac


open GlobalTheory.IndicatorVac in
theorem GlobalTheory.LocMod.indicator_vac : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k), q.UnitAA → ∀ (Y Y' : Type) [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] (S T : HSp D) (FS : Frame k S.rank Y') (FT : Frame k T.rank Y) (ψ : AddChar (AF D.host.F) ℂ) (ψk : AddChar k Circle), IsStdChar D ψ (-1) → (ofSplit q).IsChar ψ ψk → HasConductor ψk 1 → ∀ (LS : GlobalTheory.FinPl.Lat S) (LT : GlobalTheory.FinPl.Lat T), IsSelfDualC S LS → IsSelfDualC T LT → (∀ y : Y' → k, (∀ i, y i ∈ 𝒪[k]) ↔ (fun i => q.sec ((FS.β *ᵥ y) i)) ∈ GlobalTheory.FinPl.latV S LS (· = q.v)) → (∀ y : Y → k, (∀ i, y i ∈ 𝒪[k]) ↔ (fun i => q.sec ((FT.β *ᵥ y) i)) ∈ GlobalTheory.FinPl.latV T LT (· = q.v)) → (∀ Tm O, (ofSplit q).IsModel ψ FS FT Tm → IsOne O → GlobalTheory.FinPl.Vac ψ S T LS LT (· = q.v) (Tm O)) ∧ ∀ f, GlobalTheory.FinPl.Vac ψ S T LS LT (· = q.v) f → ∃ Tm, (ofSplit q).IsModel ψ FS FT Tm ∧ ∀ O, IsOne O → Tm O = f := by
  intro D k _ _ _ _ q hU Y Y' _ _ _ _ S T FS FT ψ ψk hψ hc hcond LS LT hS hT hFS hFT
  have hmono : ∀ u, u ∈ latO S T (LS : Set _) (LT : Set _) (· = q.v) → u ∈ latO S T (LS : Set _) (LT : Set _) fun _ => True :=
    fun u hu => AddSubgroup.closure_mono (fun w hw => by
      obtain ⟨α, h1, _, h3⟩ := hw
      exact ⟨α, h1, fun v hv => absurd trivial hv, h3⟩) hu
  have hsy : ∀ x : Matrix Y Y' k, (∀ r s, x r s ∈ 𝒪[k]) → ∀ u ∈ latO S T (LS : Set _) (LT : Set _) (· = q.v),
      ψ (symplO S T ((ofSplit q).up FS FT x) u) = 1 := fun x hx u hu =>
    GlobalTheory.LatVac.char_sympl_eq_one hψ hS hT (hmono _ (GlobalTheory.T.up_image_integral_matrix_mem_completed_hom_lattice D k q hU Y Y' S T FS FT LS LT hS hT hFS hFT x hx)) (hmono _ hu)
  constructor
  · intro Tm O hTm hO
    have hE : ∀ u ∈ latO S T (LS : Set _) (LT : Set _) (· = q.v), IsHalf q.e u → heisO ψ S T u (Tm O) = Tm O := by
      intro u hu he
      obtain ⟨x, hx, rfl⟩ := GlobalTheory.T.exists_integral_matrix_up_image_completed_hom_lattice D k q hU Y Y' S T FS FT LS LT hS hT hFS hFT u hu he
      refine (hTm.trans x O O fun t => ?_).symm
      rw [hO]
      have hh : (∀ r s, (t + x) r s ∈ 𝒪[k]) ↔ ∀ r s, t r s ∈ 𝒪[k] := by
        refine ⟨fun h r s => ?_, fun h r s => ?_⟩
        · have := sub_mem (h r s) (hx r s); simpa using this
        · exact add_mem (h r s) (hx r s)
      by_cases ht : ∀ r s, t r s ∈ 𝒪[k]
      · rw [Set.indicator_of_mem (show t ∈ {x : Matrix Y Y' k | ∀ r q, x r q ∈ 𝒪[k]} from ht),
          Set.indicator_of_mem (show t + x ∈ {x : Matrix Y Y' k | ∀ r q, x r q ∈ 𝒪[k]} from hh.2 ht)]
      · rw [Set.indicator_of_notMem (show t ∉ {x : Matrix Y Y' k | ∀ r q, x r q ∈ 𝒪[k]} from ht),
          Set.indicator_of_notMem (show t + x ∉ {x : Matrix Y Y' k | ∀ r q, x r q ∈ 𝒪[k]} from fun h => ht (hh.1 h))]
    have hC : ∀ u ∈ latO S T (LS : Set _) (LT : Set _) (· = q.v), IsHalf (cA D q.e) u → heisO ψ S T u (Tm O) = Tm O := by
      intro u hu he
      refine (hTm.modul u he O O fun t => ?_).symm
      rw [hO]
      by_cases ht : ∀ r s, t r s ∈ 𝒪[k]
      · rw [hsy t ht u hu, one_mul]
      · rw [Set.indicator_of_notMem (show t ∉ {x : Matrix Y Y' k | ∀ r q, x r q ∈ 𝒪[k]} from ht), mul_zero]
    refine ⟨hTm.theta O, ?_, ?_⟩
    · intro u hu
      obtain ⟨ha, hsupp⟩ := GlobalTheory.T.completed_hom_lattice_stable_split_idempotent D k q S T LS LT u hu
      set a : WO S T := Matrix.of fun i j => q.e * u i j with ha_def
      have hb : u - a ∈ latO S T (LS : Set _) (LT : Set _) (· = q.v) := sub_mem hu ha
      have hee : q.e * q.e = q.e := q.split.1
      have hce : cA D q.e * cA D q.e = cA D q.e := by rw [← map_mul, hee]
      have haH0 : IsHalf q.e a := fun i j => by
        simp only [ha_def, Matrix.of_apply]; rw [← mul_assoc, hee]
      have hbH0 : IsHalf (cA D q.e) (u - a) := fun i j => by
        have h1 : (u - a) i j = cA D q.e * u i j := by
          simp only [Matrix.sub_apply, ha_def, Matrix.of_apply]
          have := hsupp i j
          linear_combination -this
        rw [h1, ← mul_assoc, hce]
      have haH : IsHalf q.e (a + a) := fun i j => by rw [Matrix.add_apply, mul_add, haH0 i j]
      have hbH : IsHalf (cA D q.e) ((u - a) + (u - a)) := fun i j => by rw [Matrix.add_apply, mul_add, hbH0 i j]
      have h2 : (2 • u : WO S T) = (a + a) + ((u - a) + (u - a)) := by rw [two_nsmul]; abel
      have key := GlobalTheory.LatVac.heisO_heisO ψ (a + a) ((u - a) + (u - a)) (Tm O)
      rw [hC _ (add_mem hb hb) hbH, hE _ (add_mem ha ha) haH, ← h2] at key
      have hph : ψ (symplOH S T (a + a) ((u - a) + (u - a))) = 1 := by
        obtain ⟨x, hx, hxa⟩ := GlobalTheory.T.exists_integral_matrix_up_image_completed_hom_lattice D k q hU Y Y' S T FS FT LS LT hS hT hFS hFT a ha haH0
        have h3 : symplOH S T (a + a) ((u - a) + (u - a)) = symplO S T a ((u - a) + (u - a)) := by
          rw [symplOH, GlobalTheory.LatVac.symplO_add_left, mul_add, ← add_mul, ← RingHom.map_add (f := _), add_halves,
            RingHom.map_one, one_mul]
        rw [h3]
        have := hsy x hx _ (add_mem hb hb)
        rwa [← hxa] at this
      rw [hph, one_smul] at key
      exact key.symm
    · intro e' he' u hu hue
      rcases cases D k q e' he' u (GlobalTheory.T.completed_hom_lattice_stable_split_idempotent D k q S T LS LT u hu).2 hue with h | h | h
      · subst h; exact GlobalTheory.LatVac.heisO_zero ψ _
      · exact hE u hu h
      · exact hC u hu h
  · intro f hf
    have h78 := GlobalTheory.T.heisenberg_frame_half_inverse D k (ofSplit q) Y Y' S T FS FT ψ ψk hc
    have hth : IsThetaFunO ψ S T f := hf.1
    have hlv : IsLatVac (heisO ψ S T) (latO S T (LS : Set _) (LT : Set _) (· = q.v)) f := hf.2
    have h1 : ∀ x : Matrix Y Y' k, (∀ r s, x r s ∈ 𝒪[k]) → heisO ψ S T ((ofSplit q).up FS FT x) f = f :=
      fun x hx => hlv.2 q.e q.split _ (GlobalTheory.T.up_image_integral_matrix_mem_completed_hom_lattice D k q hU Y Y' S T FS FT LS LT hS hT hFS hFT x hx) (h78.1 x).1
    have h2 : ∀ y : WO S T, IsHalf (cA D (ofSplit q).e) y →
        (∀ x : Matrix Y Y' k, (∀ r s, x r s ∈ 𝒪[k]) → ψ (symplO S T ((ofSplit q).up FS FT x) y) = 1) →
        heisO ψ S T y f = f := fun y hy hann =>
      hlv.2 (cA D q.e) (splitC D k q) y
        (GlobalTheory.T.conjugate_half_annihilator_mem_completed_hom_lattice D k q hU Y Y' S T FS FT LS LT hS hT hFS hFT ψ ψk hψ hc hcond y hy hann) hy
    obtain ⟨T₁, hT₁, hT₁O⟩ := (GlobalTheory.T.localSchrodingerModel_uniq_transport_exists D k (ofSplit q) Y Y' S T FS FT ψ hψ).2.2 f hth h1 h2
    exact ⟨T₁, hT₁, fun O hO => hT₁O O hO⟩
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.LatPair GlobalTheory.SeeSaw GlobalTheory.FinPl ValuativeRel
open scoped TensorProduct nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.FinPl.BasePoint

variable {D : D7}

theorem algebraMap_placeIdem_mem {v : Pl D} {ε : AF D.host.F} (hε : IsPlaceIdem D v ε) :
    algebraMap (AF D.host.F) (AE D) ε ∈ idAt D (· = v) := by
  obtain ⟨α, rfl, -, h0⟩ := hε
  obtain ⟨hinf, hcomp⟩ := placeIdempotent_infinite_and_finite_components D v _ α rfl
  rw [mem_supportedOnPlacesIdeal_iff_components_zero_elsewhere]
  refine ⟨hinf, fun w hw => ?_⟩
  rw [hcomp, h0 w hw, TensorProduct.zero_tmul]

theorem idAt_mono {P Q : Pl D → Prop} (h : ∀ v, P v → Q v) {a : AE D} (ha : a ∈ idAt D P) : a ∈ idAt D Q := by
  rw [mem_supportedOnPlacesIdeal_iff_components_zero_elsewhere] at ha ⊢
  exact ⟨ha.1, fun w hw => ha.2 w (fun hp => hw (h w hp))⟩

theorem mulVec_mem' {I : Ideal (AE D)} {m n : ℕ} (A : Matrix (Fin m) (Fin n) (AE D)) {y : Fin n → AE D}
    (hy : ∀ i, y i ∈ I) : ∀ i, (A *ᵥ y) i ∈ I := by
  intro i
  simp only [Matrix.mulVec, dotProduct]
  exact Ideal.sum_mem _ fun j _ => I.mul_mem_left _ (hy j)

theorem mulVec_fix {V : HSp D} {e : AE D} {ε : AF D.host.F} {u v : Pl D} (hε : IsPlaceIdem D u ε)
    (he : e + cA D e = algebraMap (AF D.host.F) (AE D) ε) {h : GA D V} (hs : SuppAt e V h) (huv : v ≠ u)
    {y : Fin V.rank → AE D} (hy : ∀ l, y l ∈ idAt D (· = v)) : mt V h *ᵥ y = y := by
  have hz : ∀ l, algebraMap (AF D.host.F) (AE D) ε * y l = 0 := fun l =>
    (placeIdem_acts D u ε hε).2 _ (idAt_mono (fun w hw => by rw [hw]; exact huv) (hy l))
  have h1 : (mt V h - 1) *ᵥ y = 0 := by
    ext i
    simp only [Matrix.mulVec, dotProduct, Pi.zero_apply]
    refine Finset.sum_eq_zero fun j _ => ?_
    calc (mt V h - 1) i j * y j = (algebraMap (AF D.host.F) (AE D) ε * (mt V h - 1) i j) * y j := by
          rw [← he, hs i j]
      _ = (mt V h - 1) i j * (algebraMap (AF D.host.F) (AE D) ε * y j) := by ring
      _ = 0 := by rw [hz j, mul_zero]
  calc mt V h *ᵥ y = ((mt V h - 1) + 1) *ᵥ y := by rw [sub_add_cancel]
    _ = y := by rw [Matrix.add_mulVec, h1, Matrix.one_mulVec, zero_add]

variable {k k' : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k']

theorem pr_e_mul (q : SplitPt D k) (a : AE D) : q.pr (q.e * a) = q.pr a := by
  rw [← q.sec_pr a, q.pr_sec]

theorem e_mul_eps (q : SplitPt D k) {ε : AF D.host.F} (he : q.e + cA D q.e = algebraMap (AF D.host.F) (AE D) ε) :
    q.e * algebraMap (AF D.host.F) (AE D) ε = q.e := by
  rw [← he, mul_add, q.split.1, q.split.2.1, add_zero]

theorem map_mt_eq_one (q : SplitPt D k) (q' : SplitPt D k') (hne : q.v ≠ q'.v) {V : HSp D} {h : GA D V}
    (hs : SuppAt q'.e V h) : (mt V h).map (GlobalTheory.LocMod.ofSplit q).π = 1 := by
  show (mt V h).map q.pr = 1
  obtain ⟨ε, hε, he⟩ := q.above
  obtain ⟨ε', hε', he'⟩ := q'.above
  have h0 : q.pr (algebraMap (AF D.host.F) (AE D) ε') = 0 := by
    rw [← pr_e_mul, ← e_mul_eps q he, mul_assoc,
      (placeIdem_acts D q.v ε hε).2 _ (idAt_mono (fun w hw => by rw [hw]; exact Ne.symm hne)
        (algebraMap_placeIdem_mem hε')), mul_zero, map_zero]
  ext i j
  have hij := hs i j
  rw [he'] at hij
  have h1 : q.pr ((mt V h - 1) i j) = 0 := by rw [← hij, map_mul, h0, zero_mul]
  have e2 : (mt V h) i j = (mt V h - 1) i j + (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) i j := by simp
  rw [Matrix.map_apply, e2, map_add (f := _), h1, zero_add]
  by_cases hij' : i = j <;> simp [Matrix.one_apply, hij']

theorem xi_ne (q : SplitPt D k) : (GlobalTheory.LocMod.ofSplit q).xi ≠ 0 := by
  unfold GlobalTheory.LocMod.Place.xi GlobalTheory.LocMod.Place.pr
  intro h0
  have h1 : (GlobalTheory.LocMod.ofSplit q).π (incA D D.host.xi0) * (GlobalTheory.LocMod.ofSplit q).π (incA D D.host.xi0⁻¹) = 1 := by
    rw [← map_mul, ← map_mul, mul_inv_cancel₀ (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D), map_one, map_one]
  rw [h0, zero_mul] at h1
  exact zero_ne_one h1

theorem latV_iff_hat' (S : HSp D) (L : Lat S) (P : Pl D → Prop) (y : Fin S.rank → AE D) (hy : ∀ i, y i ∈ idAt D P) :
    y ∈ latV S L P ↔ (fun i => Formalism.IndefR.Lev.swapAE D (finPart D (y i))) ∈ GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents.hat L :=
  ⟨GlobalTheory.T.latticeCompletionAtPlaces_mem_completedHermitianLattice D S L P y, GlobalTheory.T.mem_latticeCompletionAtPlaces_of_finPart_mem_hatLattice D S L P y hy⟩

theorem finE_mulVec' (S : HSp D) (x : GA D S) (y : Fin S.rank → AE D) :
    (fun i => Formalism.IndefR.Lev.swapAE D (finPart D ((mt S x *ᵥ y) i))) =
      (Formalism.IndefR.Lev.finE S x).val *ᵥ (fun i => Formalism.IndefR.Lev.swapAE D (finPart D (y i))) := by
  have h : ((Formalism.IndefR.Lev.finE S x).val) = (mt S x).map ((Formalism.IndefR.Lev.swapAE D).comp (finPart D)) := by
    ext i j
    rfl
  rw [h]
  ext i
  exact RingHom.map_mulVec ((Formalism.IndefR.Lev.swapAE D).comp (finPart D)) (mt S x) y i

theorem exists_base (V : HSp D) (Λ L₀ : Lat V) (hΛ : IsSelfDualC V Λ) (hL₀ : IsSelfDualC V L₀) :
    ∃ t₀ ∈ GfC V, ∀ P, Moves V t₀ Λ L₀ P := by
  obtain ⟨t₀, ht₀, htr⟩ := (GlobalTheory.AdIsom.adelicIsometries D).2.2.1 V V (LinearEquiv.refl _ _) (fun _ _ => rfl) Λ L₀ hΛ hL₀
    ∅ (by intro w hw; simp at hw) 0 (fun _ => 0) (fun _ => 0) (by simp) (by simp)
  rw [LinearEquiv.refl_toLinearMap, GlobalTheory.AdIsomCorrection.mA_id, Matrix.mul_one] at htr
  refine ⟨t₀, ht₀, fun P y hy => ?_⟩
  rw [latV_iff_hat' V Λ P y hy, latV_iff_hat' V L₀ P _ (mulVec_mem' _ hy), finE_mulVec']
  exact htr.2.1 _

variable {J : Type} [Fintype J] {kk : J → Type} [∀ i, Field (kk i)] [∀ i, ValuativeRel (kk i)]
  [∀ i, TopologicalSpace (kk i)] [∀ i, IsNonarchimedeanLocalField (kk i)]

theorem exists_corr (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (q : ∀ i, SplitPt D (kk i))
    (hinj : Function.Injective (fun i => (q i).v)) (M : ∀ i, GL (Fin V.rank) (kk i)) (t₀ : GA D V) (s : Finset J) :
    ∃ g ∈ GfC V, (∀ v, (∀ i, v ≠ (q i).v) → ∀ y : Fin V.rank → AE D, (∀ l, y l ∈ idAt D (· = v)) → mt V g *ᵥ y = y) ∧
      ∀ i ∈ s, GlobalTheory.LocMod.MovedTo (GlobalTheory.LocMod.ofSplit (q i)) V (g * t₀) β (M i).val := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    exact ⟨1, one_mem _, fun v _ y _ => by rw [mt_one, Matrix.one_mulVec], fun i hi => by simp at hi⟩
  | insert j s hj ih =>
    obtain ⟨g, hg, hfix, hmv⟩ := ih
    obtain ⟨h, hsupp, hmove⟩ :=
      (GlobalTheory.T.exists_normal_frames_and_base_point_split_place D (kk j) (GlobalTheory.LocMod.ofSplit (q j)) (xi_ne (q j))).2.2 V β (M j) (g * t₀)
    refine ⟨h * g, mul_mem (GlobalTheory.WeilProduct.mem_GfC_of_suppAt (q j).split hsupp) hg, ?_, ?_⟩
    · intro v hv y hy
      rw [mt_mul, ← Matrix.mulVec_mulVec, hfix v hv y hy]
      obtain ⟨ε, hε, he⟩ := (q j).above
      exact mulVec_fix hε he hsupp (hv j) hy
    · intro i hi
      rw [Finset.mem_insert] at hi
      rcases hi with rfl | hi
      · rw [mul_assoc]; exact hmove
      · intro b hb
        have hij : (q i).v ≠ (q j).v := fun h' => hj (by rw [← (hinj h' : i = j)]; exact hi)
        rw [mul_assoc, mt_mul, Matrix.mul_assoc, Matrix.map_mul, map_mt_eq_one (q i) (q j) hij hsupp, Matrix.one_mul]
        exact hmv i hi b hb

end GlobalTheory.FinPl.BasePoint


open GlobalTheory.FinPl.BasePoint in
theorem GlobalTheory.FinPl.BasePoint.exists_move : ∀ (D : D7) (V : HSp D) (Λ L₀ : Lat V) (β : GL (Fin V.rank) (Lev.EAf D)), IsSelfDualC V Λ → IsSelfDualC V L₀ → ∀ (J : Type) [Fintype J] (k : J → Type) [∀ i, Field (k i)] [∀ i, ValuativeRel (k i)] [∀ i, TopologicalSpace (k i)] [∀ i, IsNonarchimedeanLocalField (k i)] (q : ∀ i, SplitPt D (k i)), Function.Injective (fun i => (q i).v) → ∀ M : ∀ i, GL (Fin V.rank) (k i), ∃ t ∈ GfC V, ∃ L : Lat V, IsSelfDualC V L ∧ (∀ P, Moves V t Λ L P) ∧ (∀ v, (∀ i, v ≠ (q i).v) → latV V L (· = v) = latV V L₀ (· = v)) ∧ ∀ i, GlobalTheory.LocMod.MovedTo (GlobalTheory.LocMod.ofSplit (q i)) V t β (M i).val := by
  intro D V Λ L₀ β hΛ hL₀ J _ kk _ _ _ _ q hinj M
  obtain ⟨t₀, ht₀, hmv₀⟩ := exists_base V Λ L₀ hΛ hL₀
  obtain ⟨g, hg, hfix, hmv⟩ := exists_corr V β q hinj M t₀ Finset.univ
  obtain ⟨L, hL, hmoves⟩ := (GlobalTheory.T.selfDual_image_adelicPoint_wittCore D V Λ hΛ).1 (g * t₀)
  refine ⟨g * t₀, mul_mem hg ht₀, L, hL, hmoves, ?_, fun i => hmv i (Finset.mem_univ i)⟩
  intro v hv
  ext y
  by_cases hy : ∀ l, y l ∈ idAt D (· = v)
  · have hz : ∀ l, (mt V t₀⁻¹ *ᵥ y) l ∈ idAt D (· = v) := mulVec_mem' _ hy
    have h1 : mt V t₀ *ᵥ (mt V t₀⁻¹ *ᵥ y) = y := by
      rw [Matrix.mulVec_mulVec, ← mt_mul, mul_inv_cancel, mt_one, Matrix.one_mulVec]
    have h2 : mt V (g * t₀) *ᵥ (mt V t₀⁻¹ *ᵥ y) = y := by
      rw [mt_mul, ← Matrix.mulVec_mulVec, h1, hfix v hv y hy]
    have a1 := hmoves (· = v) _ hz
    have a2 := hmv₀ (· = v) _ hz
    rw [h2] at a1
    rw [h1] at a2
    exact a1.symm.trans a2
  · have hsupp : ∀ (N : Lat V), IsSelfDualC V N → y ∉ latV V N (· = v) := fun N hN hyN =>
      hy (((GlobalTheory.T.adelicPoint_components_atPlaces_lattices_vacua D (· = v)).2 V).2.2.2 N y hN.1 |>.1 hyN).1
    exact iff_of_false (hsupp L hL) (hsupp L₀ hL₀)
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StepData GlobalTheory.SplitWeil ValuativeRel

noncomputable section

theorem GlobalTheory.LocRed.red_entry_movedFrame : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k) (PP : Formalism.L2.DIV.Pl D.host.E), Formalism.L2.NTheta.IsIdemAt q.e PP → ∀ (ϖ : kˣ), GlobalTheory.SymBridge.IsCompl PP (Formalism.L2.Col.qOf PP) (q.pr.comp (incA D)) ϖ → ∀ (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (N : ℕ), IsSDFrame V β Λ N → ∀ (Y : Type) [Fintype Y] [DecidableEq Y] (F : GlobalTheory.LocMod.Frame k V.rank Y) (σ : Fin V.rank ≃ Y) (b : GA D V), MovedTo (ofSplit q) V b β (F.β.submatrix id σ) → ∀ (g : GA D V) (gk : GL Y k), (ofSplit q).IsLoc F g gk → Lev.finE V (b⁻¹ * g * b) ∈ Formalism.L2.DIV.St β → ∀ (a a' : Fin V.rank) (z : 𝓞 D.host.E), (Formalism.L2.DIV.redFn β PP (Lev.finE V (b⁻¹ * g * b))).val a a' = Ideal.Quotient.mk PP.asIdeal z → valuation k (gk.val (σ a) (σ a') - (ofSplit q).pr (z : D.host.E)) < 1 := by
  intro D k _ _ _ _ q PP hPP ϖ _ V β Λ N _ Y _ _ F σ b hb g gk hg hSt a a' z hz
  have hM : (mt V g).map q.pr * F.β.submatrix id σ = F.β.submatrix id σ * gk.val.submatrix σ σ := by
    have h1 : (mt V g).map q.pr = F.β * gk.val * F.γ := hg.2
    have hs : ∀ A : Matrix (Fin V.rank) (Fin V.rank) k, A * F.β.submatrix id σ = (A * F.β).submatrix id σ := fun A => by
      ext i j; simp [Matrix.mul_apply]
    rw [h1, Matrix.submatrix_mul_equiv F.β gk.val id σ σ, hs, Matrix.mul_assoc (F.β * gk.val), F.γβ, Matrix.mul_one]
  have key := GlobalTheory.SeeSaw.LevRed.red_of_movedTo q PP hPP V β b g _ _ hb hM hSt a a' z hz.symm
  simpa [Matrix.submatrix_apply] using key

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.lower_block_parameter_twist_L_factor : ∀ (D : D7) (c : Com D) (w : Twist D), w.Is c → ∀ k < D.R.m, ∀ PP ∈ w.Q, ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (φ : SplitProj D v), IsProjAt φ PP → ∀ x ϖ, IsLocUnif φ x ϖ → (∀ z t, GlobalTheory.LFun.seg PP z t = GlobalTheory.ParHecke.segL ϖ z t) ∧ (qPar c PP x k).card = k * D.R.t ∧ ∀ α : Fin (k * D.R.t) → ℂˣ, Finset.univ.val.map α = (qPar c PP x k).map (· * (Circle.toUnits (c.chT (k + 1) x))⁻¹) → (∀ i, ‖(α i : ℂ)‖ ≤ (Ideal.absNorm PP.asIdeal : ℝ) ^ (((D.R.t : ℝ) - 1) / 2) ∧ ‖(α i : ℂ)‖⁻¹ ≤ (Ideal.absNorm PP.asIdeal : ℝ) ^ (((D.R.t : ℝ) - 1) / 2)) ∧ GlobalTheory.GLDoubling.lFactor (Ideal.absNorm PP.asIdeal) α ((D.R.t : ℂ) / 2 + 1 / 2) * GlobalTheory.GLDoubling.lFactor (Ideal.absNorm PP.asIdeal) α⁻¹ ((D.R.t : ℂ) / 2 + 1 / 2) * GlobalTheory.GLDoubling.invNormFactor (Ideal.absNorm PP.asIdeal) (k * D.R.t) ((D.R.t : ℂ) / 2) = blockL c k PP * (zinv PP D.R.t ((k + 1) * D.R.t) : ℂ) := by
  first | exact @GlobalTheory.ChainTw.qPar_twist_lFactor | exact GlobalTheory.ChainTw.qPar_twist_lFactor | (intros; apply GlobalTheory.ChainTw.qPar_twist_lFactor <;> assumption)
end
