module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle657
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle617
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle515
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasInfExpOfOrder
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle187
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle211
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle529
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsOrthogonalSumLatticeSameLatticedSpace
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsBplusNeZero
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PathConvergenceDownChain
import Formalism.LocalToGlobal.Divisibility.DefGroupLemmas
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle451
public import Mathlib.Analysis.Matrix.MeasurableSpace
public import Formalism.DoubleCosetMeasures.StatementZ
public import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1855
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle404
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumOKEx
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnderMemAndPlaceAboveEqOfMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationLeOneOfMem
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
import Development.AutomorphicArithmetic.CyclotomicBounds.RamifiedDiscriminants.Bundle001
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle375
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle367
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
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle468
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle287
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle324

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries
open scoped TensorProduct Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.RowReal

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

theorem hasInfExp_attChr_chi {μ0 : T} (hL : L.Is μ0) {i : ℕ} (hi : i < D.R.m) (n : ℕ) (τ : D.what₂.Tau) :
    HasInfExp D (Formalism.IndefR.Lift.attChr (G.ch.chi (D.R.m - i)) L.eta n) τ
      ((cen D sc.cGap τ (D.R.m - i) : ℚ) - if Odd n then 1 / 2 else 0) := by
  have hm1 : 1 ≤ D.R.m - i := by omega
  have hm2 : D.R.m - i ≤ D.R.m := by omega
  have h0 : HasInfExp D (G.ch.chi (D.R.m - i)) τ (cen D sc.cGap τ (D.R.m - i) : ℚ) :=
    GlobalTheory.HeckeInfExp.hasInfExp_of_chrEq D _ _ (fun τ => (cen D sc.cGap τ (D.R.m - i) : ℚ)) (G.ch.chi_eq _ hm1 hm2)
      ⟨fun τ => 2 * cen D sc.cGap τ (D.R.m - i), fun τ => by push_cast; ring, G.ch.inf _ hm1 hm2⟩ τ
  have heta : HasInfExp D L.eta τ (1 / 2) :=
    GlobalTheory.HeckeInfExp.hasInfExp_of_chrEq D _ _ _ hL.eta
      (GlobalTheory.Chain.StepVac.hasInfQ_tau (a := fun _ => 1 / 2) ⟨_, fun _ => by norm_num, L.C.isEta.inf⟩) τ
  unfold Formalism.IndefR.Lift.attChr
  split_ifs
  · rw [sub_eq_add_neg]
    exact GlobalTheory.Chain.StepVac.hasInfExp_mul h0 (GlobalTheory.Chain.StepVac.hasInfExp_inv heta)
  · simpa using h0

theorem rowEntries_c_rev (τ : D.what₂.Tau) (i : Fin D.R.m) :
    (rowEntries D sc.cGap τ).c i.rev = cen D sc.cGap τ (D.R.m - i) := by
  show (num D sc.cGap τ).cen ((i.rev : ℕ) + 1) = _
  rw [Fin.val_rev, show D.R.m - (i + 1) + 1 = D.R.m - i by omega]
  rfl

theorem half_ceil (n : ℕ) : (((n + 1) / 2 : ℕ) : ℚ) = (n : ℚ) / 2 + if Odd n then 1 / 2 else 0 := by
  rcases Nat.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
  · rw [if_neg (Nat.not_odd_iff_even.2 ⟨k, hk⟩), hk, show (k + k + 1) / 2 = k by omega]
    push_cast; ring
  · rw [if_pos ⟨k, hk⟩, hk, show (2 * k + 1 + 1) / 2 = k + 1 by omega]
    push_cast; ring

theorem det_compAt_ptGrid {μ0 : T} (hL : L.Is μ0) (W : G.Weil) (g : Gc D.what₂.Tau (rowSizes D)) (n : ℕ) (hn : n < D.R.m + 1)
    (τ : D.what₂.Tau) :
    (compAt W.θ τ (Formalism.L2.Theta.mt (G.V (.grid n D.R.m)) (ptGrid W g n))).det =
      Matrix.det (g.2 ⟨n, hn⟩ τ).1 := by
  have hX : DefNode D.R.m (.grid n D.R.m) := ⟨Nat.lt_succ_iff.1 hn, rfl⟩
  have hW := posOnb_of_defNode W μ0 hL hX
  have hB : IsUnit (W.onb (.grid n D.R.m) τ).det := by
    have h := congrArg Matrix.det (hW τ)
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_one] at h
    exact isUnit_iff_ne_zero.2 fun h0 => by rw [h0, mul_zero] at h; exact zero_ne_one h
  rw [ptGrid_le W g hn, compAt_kappa_snd g ⟨n, hn⟩ hW τ, Matrix.det_mul, Matrix.det_mul, Matrix.det_nonsing_inv,
    mul_right_comm, Ring.mul_inverse_cancel _ hB, one_mul]
  exact Matrix.det_submatrix_equiv_self (finCongr (rank_gridM G (Nat.lt_succ_iff.1 hn))) _

theorem om_ptGrid_movedVec : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ0 : T}, L.Is μ0 →
    ∀ (W : G.Weil) {U : Set T} (S : GridChoice W U) (g : Gc D.what₂.Tau (GlobalTheory.RowReal.rowSizes D)) (t : T) (i : Fin D.R.m)
    (d : FinDatum G t (.chi i D.R.m)), S.Z.HasVec d →
    W.om (.chi i D.R.m) (G.toPair (.chi i D.R.m) (GlobalTheory.RowReal.ptGrid W g i) (GlobalTheory.RowReal.ptGrid W g (i + 1))) (movedVec t S d) =
      GlobalTheory.RowReal.colScal (GlobalTheory.RowReal.rowEntries D sc.cGap) i g • movedVec t S d := by
  intro D T L sc G μ0 hL W U S g t i d hd
  have hp : DefPair D.R.m (.chi (i : ℕ) D.R.m : Pair T) := ⟨i.2, rfl⟩
  have hn := DefPair.nodes hp
  have hom := W.om_is (.chi (i : ℕ) D.R.m) (by
    simp only [DefPair, DefNode] at hp hn; simp only [Pair.InRange, Node.InRange]; omega)
  obtain ⟨h1, h2⟩ := GlobalTheory.T.gridFiniteDatumVector_theta_fockVacuum W S.Z hp d hd
  have hf : IsThetaFunO W.ψ _ _ (movedVec t S d) ∧ ∀ τ, IsFockVacAt (heisO W.ψ _ _) W.θ τ
      (cplxO (G.cartS W.cart (.chi (i : ℕ) D.R.m) τ) (G.onT W.cart (.chi (i : ℕ) D.R.m) τ)) (movedVec t S d) :=
    GlobalTheory.T.weil_finitePoint_preserves_fockVacuum D W.ψ W.θ _ _ _ _ (W.om _) hom W.θ_is _ _ _ h1 h2 _
      (GlobalTheory.FockReal.negGA_mem_GfC _ (S.N.u _).2) _ (S.N.u _).2
  have hrS : (G.pS (.chi (i : ℕ) D.R.m : Pair T)).rank = (rowSizes D).nC ((i : ℕ) + 1) := rank_gridM G (by omega)
  have hrT : (G.pT (.chi (i : ℕ) D.R.m : Pair T)).rank = (rowSizes D).nC (i : ℕ) := rank_gridM G (by omega)
  have key := GlobalTheory.FockReal.om_fockIn hL W W.onb hp (fun X hX τ => GlobalTheory.FockReal.onb_def hL W hX τ)
    (fun τ => (cen D sc.cGap τ (D.R.m - i) : ℚ) - if Odd (G.pS (.chi (i : ℕ) D.R.m : Pair T)).rank then 1 / 2 else 0)
    (fun τ => (cen D sc.cGap τ (D.R.m - i) : ℚ) - if Odd (G.pT (.chi (i : ℕ) D.R.m : Pair T)).rank then 1 / 2 else 0)
    (fun τ => hasInfExp_attChr_chi hL i.2 _ τ) (fun τ => hasInfExp_attChr_chi hL i.2 _ τ)
    (fun τ => (rowEntries D sc.cGap τ).c i.rev - (((rowSizes D).nC i.succ + 1) / 2 : ℕ))
    (fun τ => -(rowEntries D sc.cGap τ).c i.rev + (((rowSizes D).nC i.castSucc + 1) / 2 : ℕ))
    (fun τ => ?_) (fun τ => ?_) _ hf.1 hf.2 (ptGrid W g i) (ptGrid_mem W g i) (ptGrid W g (i + 1))
    (ptGrid_mem W g (i + 1)) 1
  · have e1 : fockIn W W.onb (.chi (i : ℕ) D.R.m) (movedVec t S d) 1 = movedVec t S d :=
      GlobalTheory.FiniteFock.pureTensorO_one _ _ _ _ _ _ _ _ _
    rw [show GlobalTheory.FockReal.realSubst W W.onb (.chi (i : ℕ) D.R.m) (ptGrid W g i) (ptGrid W g (i + 1)) 1 = 1 from
      map_one _, e1] at key
    rw [key]
    congr 1
    simp only [GlobalTheory.FockReal.realChar, GridData.toPair, mt_negGA]
    simp only [det_compAt_ptGrid hL W g (i : ℕ) (by omega), det_compAt_ptGrid hL W g ((i : ℕ) + 1) (by omega)]
    simp only [colScal, detChar, detU, MonoidHom.coe_mk, OneHom.coe_mk, Units.val_mul, Units.coe_prod,
      Units.val_zpow_eq_zpow_val, MonoidHom.coe_toHomUnits, MonoidHom.coe_comp, Function.comp_apply]
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [mul_comm]
    rfl
  · simp only [GlobalTheory.FockReal.sgnP, rowEntries_c_rev, Fin.val_succ, rank_gridM G (show (i : ℕ) + 1 ≤ D.R.m by omega),
      Int.cast_sub, Int.cast_natCast, half_ceil]
    ring
  · simp only [GlobalTheory.FockReal.sgnP, rowEntries_c_rev, Fin.val_castSucc, hrT, Int.cast_add, Int.cast_neg, Int.cast_natCast,
      half_ceil]
    ring

end GlobalTheory.RowReal
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.GridMeasDown

open GlobalTheory.GridJoin GlobalTheory.Grid

variable {D : D7}

theorem exch {V₁ V₂ : HSp D} (hV : SameSp V₂ V₁) (e : GA D V₁ = GA D V₂)
    {μ₁ : Measure (GA D V₁)} {F₁ : Set (GA D V₁)} {μ₂ : Measure (GA D V₂)} {F₂ : Set (GA D V₂)}
    (hμ : HEq μ₁ μ₂) (hH₂ : μ₂.IsHaarMeasure) (h1 : IsFundamentalDomain (GQ V₁) F₁ μ₁)
    (h2 : IsFundamentalDomain (GQ V₂) F₂ μ₂) (H : GA D V₂ → ℂ) (hH : ∀ γ ∈ GQ V₂, ∀ g, H (γ * g) = H g) :
    (IntegrableOn (fun g => H (cast e g)) F₁ μ₁ ↔ IntegrableOn H F₂ μ₂) ∧
      ∫ g in F₁, H (cast e g) ∂μ₁ = ∫ g in F₂, H g ∂μ₂ := by
  obtain ⟨L, hl1, hl2, rfl⟩ := hV
  obtain rfl : μ₁ = μ₂ := eq_of_heq hμ
  exact GlobalTheory.FlipStart.Col.fund_exch (V := V₂) (μ := μ₁) h1 h2 H hH

theorem measFD_heq {V V₀ : HSp D} (hV : SameSp V₀ V) {K : Subgroup (GL (Fin V.rank) (Lev.EAf D))}
    {K₀ : Subgroup (GL (Fin V₀.rank) (Lev.EAf D))} (hK : HEq K K₀) {μ : Measure (GA D V)} {μ₀ : Measure (GA D V₀)}
    {F : Set (GA D V)} {F₀ : Set (GA D V₀)} (h : Lev.IsMeasFD V K μ F) (h₀ : Lev.IsMeasFD V₀ K₀ μ₀ F₀) : HEq μ μ₀ := by
  obtain ⟨L, hl1, hl2, rfl⟩ := hV
  obtain rfl := eq_of_heq hK
  exact heq_of_eq (GlobalTheory.FunObjModel.isMeasLevW_unique (V := V₀) (fun _ _ e => e.1) h.1 h₀.1)

theorem measDef_heq {V V₀ : HSp D} (hV : SameSp V₀ V) {K : Subgroup (GL (Fin V.rank) (Lev.EAf D))}
    {K₀ : Subgroup (GL (Fin V₀.rank) (Lev.EAf D))} (hK : HEq K K₀) {μ : Measure (GA D V)} {μ₀ : Measure (GA D V₀)}
    {F : Set (GA D V)} {F₀ : Set (GA D V₀)} (h : IsMeasDef V K μ F) (h₀ : IsMeasDef V₀ K₀ μ₀ F₀) : HEq μ μ₀ := by
  obtain ⟨L, hl1, hl2, rfl⟩ := hV
  obtain rfl := eq_of_heq hK
  have h1 : Lev.IsMeasLevDef V₀ K μ := h.1
  exact heq_of_eq (GlobalTheory.FunObjModel.isMeasLevW_unique (V := V₀) (fun _ _ e => e.1) h1 h₀.1)

theorem lev_heq {V V' : HSp D} (hsp : SameSp V V') {β : GL (Fin V'.rank) (Lev.EAf D)}
    {Λ' : Submodule (𝓞 D.host.E) (Fin V'.rank → D.host.E)} {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)}
    (hl : HEq Λ' Λ) (hf : Formalism.L2.DIV.IsFrame β Λ') :
    HEq (UA D.sp.cm V'.gram ⊓ St β) (GlobalTheory.ChiGrid.congLev D.sp.cm V.gram Λ ⊤) := by
  obtain ⟨L, hl1, hl2, rfl⟩ := hsp
  obtain rfl := eq_of_heq hl
  have hs := Formalism.L2.DIV.stabilizer_eq_stabilizer_lattice _ _ _ _ _ hf
  have h2 := GlobalTheory.ChiGrid.congLev_top (hc := D.sp.cm) (J := V.gram) (Λ := Λ')
  apply heq_of_eq
  rw [h2, hs]
  rfl

theorem cast_heq {S S' : GlobalTheory.Grid.Node D} (h : S = S') (m : S.MeasDat) :
    HEq (Node.MeasDat.cast h m).ν m.ν ∧ HEq (Node.MeasDat.cast h m).fd m.fd := by
  subst h; exact ⟨HEq.rfl, HEq.rfl⟩

theorem cast_fd {S S' : GlobalTheory.Grid.Node D} (h : S = S') (m : S.MeasDat) (hf : IsFundamentalDomain (GQ S.V) m.fd m.ν) :
    IsFundamentalDomain (GQ S'.V) (Node.MeasDat.cast h m).fd (Node.MeasDat.cast h m).ν := by
  subst h; exact hf

theorem meas_down : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {sc : Consts} {large₂ : SizeData₂ D}
    {F : Face D A}, GlobalTheory.RowClaim.HidaSetting large₂ R F → sc.cGap = 1 →
    ∀ {G' : GridData R.toLevCh sc} (W : G'.Weil), W.Over R → ∀ G : GlobalTheory.Grid.GridPre R, G.Is → GlobalTheory.GridJoin.Match G W →
    ∀ (M : Vol G') (t : T), M.Is t → ∀ (i j : ℕ), i ≤ D.R.m → j < D.R.m →
    ∀ (e : GA D (G.V i (j + 1)).V = GA D (G'.V (.grid i (j + 1)))) (H : GA D (G'.V (.grid i (j + 1))) → ℂ),
    (∀ γ ∈ GQ (G'.V (.grid i (j + 1))), ∀ g, H (γ * g) = H g) →
    (IntegrableOn (fun g => H (cast e g)) (G.meas t i (j + 1)).fd (G.meas t i (j + 1)).ν ↔
      IntegrableOn H (M.fd (.grid i (j + 1))) (M.ν (.grid i (j + 1)))) ∧
    ∫ g in (G.meas t i (j + 1)).fd, H (cast e g) ∂(G.meas t i (j + 1)).ν =
      ∫ g in M.fd (.grid i (j + 1)), H g ∂(M.ν (.grid i (j + 1))) := by
  intro D Γ _ _ Pl0 T A Ks _ _ _ R sc large₂ F hS hc G' W hW G hG hJ M t hM i j hi hj e H hH
  have hAt := hM.vtx (.grid i (j + 1)) ⟨hi, by omega⟩
  obtain ⟨hHaar, hfd⟩ := hAt.haar_fund
  have hsp : SameSp (G'.V (.grid i (j + 1))) (G.V i (j + 1)).V := (hJ.1.vert i (j + 1) hi (by omega)).sp
  suffices key : HEq (G.meas t i (j + 1)).ν (M.ν (.grid i (j + 1))) ∧
      IsFundamentalDomain (GQ (G.V i (j + 1)).V) (G.meas t i (j + 1)).fd (G.meas t i (j + 1)).ν from
    exch hsp e key.1 hHaar key.2 hfd H hH
  unfold Vol.IsAt at hAt
  rcases i with _ | i
  · have hmod := hS.core.models
    by_cases h : j + 1 < D.R.m
    · have hT : G'.V (.grid 0 (j + 1)) = Yc D (j + 1) := congrArg LSp.sp (colY_lt R.toLevCh h)
      have hK : HEq (levJ G' t (.grid 0 (j + 1)))
          (lev D.sp.cm (Yc D (j + 1)).gram (R.βY (j + 1)) (R.datYt t (j + 1) R.triv)) := levCol_lt R.toLevCh t h
      have e0 : G.meas t 0 (j + 1) = Node.MeasDat.cast (nodeY_eq_chainVertexAtRowZero_of_lt R h) ⟨R.νY t (j + 1), R.fdY t (j + 1)⟩ := by
        show meas0 R t j = _
        rw [meas0, dite_eq_left h]
      rw [e0]
      rcases Nat.lt_or_ge (j + 1 + 1) D.R.m with h' | h'
      · have hc := hmod.νY t (j + 1) h'
        rw [if_neg (show ¬ (GlobalTheory.ChiGrid.Node.grid 0 (j + 1)).neg D.R.m = 0 by simp only [GlobalTheory.ChiGrid.Node.neg]; omega)] at hAt
        exact ⟨(cast_heq _ _).1.trans (GlobalTheory.FlipStart.Col.measFD_heq hT hK hAt hc).symm, cast_fd _ _ hc.2⟩
      · have e1 : j + 1 = D.R.m - 1 := by omega
        have hc := hmod.νY' t
        rw [← e1] at hc
        rw [if_pos (show (GlobalTheory.ChiGrid.Node.grid 0 (j + 1)).neg D.R.m = 0 by simp only [GlobalTheory.ChiGrid.Node.neg]; omega)] at hAt
        exact ⟨(cast_heq _ _).1.trans (GlobalTheory.FlipStart.Col.measDef_heq hT hK hAt hc).symm, cast_fd _ _ hc.2⟩
    · have hj' : j + 1 = D.R.m := by omega
      have hT : G'.V (.grid 0 (j + 1)) = D.sp.X' := by
        show (columnBlock R.toLevCh (j + 1)).sp = _
        rw [hj', colY_m]
      have hK : HEq (levJ G' t (.grid 0 (j + 1))) (lev D.sp.cm D.sp.X'.gram R.βX (R.datXt t)) := levCol_top R.toLevCh t h
      have e0 : G.meas t 0 (j + 1) = Node.MeasDat.cast (nodeX_eq_chainVertexAtRowZero_of_ge R h) ⟨R.νX t, R.fdX t⟩ := by
        show meas0 R t j = _
        rw [meas0, dite_eq_right h]
      rw [e0]
      have hc := hmod.νX t
      rw [if_pos (show (GlobalTheory.ChiGrid.Node.grid 0 (j + 1)).neg D.R.m = 0 by simp only [GlobalTheory.ChiGrid.Node.neg]; omega)] at hAt
      exact ⟨(cast_heq _ _).1.trans (GlobalTheory.FlipStart.Col.measDef_heq hT hK hAt hc).symm, cast_fd _ _ hc.2⟩
  · have hN := hJ.1.vert (i + 1) (j + 1) hi (by omega)
    have hm := hG.meas.vert i j hi (by omega)
    obtain ⟨c, hfr⟩ := (hG.spaces.vert i (j + 1) hi (by omega)).frame
    have hK : HEq ((G.nV i (j + 1)).princ ⊤) (levJ G' t (.grid (i + 1) (j + 1))) := by
      rw [GlobalTheory.Grid.Node.princ_top]
      exact lev_heq hN.sp hN.lat hfr.1
    show HEq (G.mV i (j + 1)).ν _ ∧ IsFundamentalDomain (GQ (G.nV i (j + 1)).V) (G.mV i (j + 1)).fd (G.mV i (j + 1)).ν
    by_cases hd : D.R.m - 1 ≤ j + 1
    · have h1 := hm.1 hd
      rw [if_pos (show (GlobalTheory.ChiGrid.Node.grid (i + 1) (j + 1)).neg D.R.m = 0 by simp only [GlobalTheory.ChiGrid.Node.neg]; omega)] at hAt
      exact ⟨measDef_heq hN.sp hK h1 hAt, h1.2⟩
    · have h1 := hm.2 hd
      rw [if_neg (show ¬ (GlobalTheory.ChiGrid.Node.grid (i + 1) (j + 1)).neg D.R.m = 0 by simp only [GlobalTheory.ChiGrid.Node.neg]; omega)] at hAt
      exact ⟨measFD_heq hN.sp hK h1 hAt, h1.2⟩

end GlobalTheory.GridMeasDown
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest Formalism.IndefR.WeilFull GlobalTheory.RowClaim
open MeasureTheory GlobalTheory.SplitFlip GlobalTheory.SplitWeil

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.FlipIntegrand

theorem pde_ne_q_of_setting {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {large₂ : SizeData₂ D} {F : Face D A}
    (h : HidaSetting large₂ R F) : Nat.Coprime D.host.pde (D.host.QS * D.host.q) ∧ Nat.Coprime D.host.pde' (D.host.QS * D.host.q) := by
  obtain ⟨⟨P, -, -⟩, -⟩ := h.size
  have key : ∀ p ∈ D.host.levelPrimes, p.Prime → Nat.Coprime p (D.host.QS * D.host.q) := fun p hp hpp =>
    UpperTheory.Ram.Fun.coprime_QSq_of_splitK D.host hpp (P.level_split p hp)
  exact ⟨key _ D.host.pde_level.1 D.host.pde_prime, key _ D.host.pde_level.2 D.host.pde'_prime⟩

theorem flatIntegrand_lc_cpt : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (ch : Choice R) (large₂ : SizeData₂ D) (F : Face D A) (CF b : ℝ), HidaSetting large₂ R F → ch.Is → ch.AtScale CF b → ch.FieldOK → ∀ (t : T) (Φ : ch.G.Datum), ch.S.SumOK t Φ → ∀ β ∈ ch.S.supp t Φ, ∀ (w : locPl ch.G t) X Y, IsLocallyConstant (flatIntegrand one_le_sLen (psiAt ch.W w.1) (moved (locGrid ch.G t w) (keepAt ch.G w) ((repsAt ch.G t w).elt (β w)) (Tflip ch.W ch.S.B t Φ w)) X Y) ∧ HasCompactSupport (flatIntegrand one_le_sLen (psiAt ch.W w.1) (moved (locGrid ch.G t w) (keepAt ch.G w) ((repsAt ch.G t w).elt (β w)) (Tflip ch.W ch.S.B t Φ w)) X Y) := by
  intro D Γ _ _ Pl0 T A Ks _ _ _ R ch large₂ F CF b hS hch _ _ t Φ _ β _ w X Y
  have hL : R.toLevCh.Is A.μ0 := hS.core.lev
  have hde := pde_ne_q_of_setting hS
  have hc : ∀ P ∈ R.toLevCh.Q t, ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal := hch.guard t
  have hT := isTensor_Tflip hL ch.W ch.S.B t Φ hde hc w.2
  have hm : 0 < D.R.m := by have := D.R.two_le_m; omega
  have hcond : HasConductor (psiAt ch.W w.1) 1 :=
    (((Good.locGrid_isGood hL ch.G ch.W t hde hc).1 w.1 w.2).square 0 hm 0 hm).cond
  refine ⟨?_, hasCompactSupport_flatIntegrand one_le_sLen _ hT _ _ X Y⟩
  have hmv : Continuous ((locGrid ch.G t w).moveArgs .one ((repsAt ch.G t w).elt (β w))) := continuous_pi fun b =>
    (continuous_const.matrix_mul (continuous_apply b)).matrix_mul continuous_const
  have hψ : IsLocallyConstant fun e => ((psiAt ch.W w.1 (-phase X e) : Circle) : ℂ) :=
    ((hcond.isLocallyConstant.comp Subtype.val).comp_continuous (continuous_phase X).neg)
  exact ((IsLocallyConstant.const _).mul ((IsLocallyConstant.const _).mul
    ((isLocallyConstant_of_isTensor hT).comp_continuous (hmv.comp (continuous_fill one_le_sLen X Y))))).mul hψ

end GlobalTheory.FlipIntegrand
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.FlipRun

theorem canFlip_of_append {γ : List GlobalTheory.SplitFlip.Edge} {l l' : List (ℕ × ℕ)} (h : GlobalTheory.SplitFlip.CanFlip γ (l ++ l')) :
    GlobalTheory.SplitFlip.CanFlip γ l := by
  induction l generalizing γ with
  | nil => exact .nil _
  | cons x l ih =>
    cases h with
    | cons hp h' => exact .cons hp (ih h')

theorem isTensor_flips_take : GlobalTheory.RowClaim.Big fun {D} _ _ _ _ {T} _ _ _ _ _ _ ch => ∀ (t : T) (Φ : ch.G.Datum), ∀ w ∈ locPl ch.G t, ∀ k, k ≤ D.R.m ^ 2 → (locGrid ch.G t w).IsTensor (unifAt w) (depthAt ch.G w) ((givenStage t w ch.S.B Φ).flips .one (psiAt ch.W w) (unifAt w) (depthAt ch.G w) ((flipOrder D.R.m).take k)).path ((givenStage t w ch.S.B Φ).flips .one (psiAt ch.W w) (unifAt w) (depthAt ch.G w) ((flipOrder D.R.m).take k)).tensor := by
  refine ⟨0, fun ε CF _ => ⟨0, fun D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F s ch hch _ => ?_⟩⟩
  intro t Φ w hw k _
  have hL := s.core.lev
  have hde : Nat.Coprime D.host.pde (D.host.QS * D.host.q) ∧ Nat.Coprime D.host.pde' (D.host.QS * D.host.q) := by
    obtain ⟨⟨P, -, -⟩, -⟩ := s.size
    have key : ∀ p ∈ D.host.levelPrimes, p.Prime → Nat.Coprime p (D.host.QS * D.host.q) := fun p hp hpp =>
      UpperTheory.Ram.Fun.coprime_QSq_of_splitK D.host hpp (P.level_split p hp)
    exact ⟨key _ D.host.pde_level.1 D.host.pde_prime, key _ D.host.pde_level.2 D.host.pde'_prime⟩
  have hg := (Good.locGrid_isGood hL ch.G ch.W t hde (hch.guard t)).1 w hw
  have hadm := GivenAdm.givenStage_isAdmissible hL ch.S.B t Φ hw
  have hm : 0 < D.R.m := by have := D.R.two_le_m; omega
  have h00 := hg.square 0 hm 0 hm
  have hν : ∀ x ∈ flipOrder D.R.m, GlobalTheory.SplitFlip.CondLE (unifAt w) (depthAt ch.G w) ((locGrid ch.G t w).nu x.1 x.2) := by
    intro x hx
    simp only [flipOrder, List.mem_flatMap, List.mem_map, List.mem_range] at hx
    obtain ⟨i, hi, j, hj, rfl⟩ := hx
    rw [← GlobalTheory.SplitFlip.Grid.alpha_div_beta]
    exact (hg.square i hi j hj).condν
  have hcan : GlobalTheory.SplitFlip.CanFlip (GlobalTheory.SplitFlip.givenPath D.R.m) ((flipOrder D.R.m).take k) := by
    have h := (canFlip_flipOrder D.R.m).1
    rw [← List.take_append_drop k (flipOrder D.R.m)] at h
    exact canFlip_of_append h
  exact isTensor_flips h00.unif h00.cond h00.one_le ((flipOrder D.R.m).take k) (givenStage t w ch.S.B Φ)
    (fun x hx => hν x (List.mem_of_mem_take hx)) hcan (fun X => GivenAdm.givenLevel_open hL hw X) hadm.tensor

end GlobalTheory.FlipRun

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopLevelInv

noncomputable section

namespace GlobalTheory.SquareFlipCols

theorem squareFlip_blockDiag_cols : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] {A A' D₁ D₂ : Type} [Fintype A] [DecidableEq A] [Fintype A'] [DecidableEq A'] [Fintype D₁] [DecidableEq D₁] [Fintype D₂] [DecidableEq D₂]
    (μ : Measure (GL A' k)) [μ.IsHaarMeasure] (σ : A ⊕ A' ≃ D₁ ⊕ D₂) (ψ : AddChar k Circle) (ν : kˣ →* ℂˣ) (ϖ : kˣ) (e : ℕ),
    IsUnif ϖ → HasConductor ψ 1 → 1 ≤ e → CondLE ϖ e ν → ∀ Φ : Matrix A' (D₁ ⊕ D₂) k → ℂ, IsNatDatum ϖ e Φ →
    ∀ M₁ ∈ KO k D₁, ∀ M₂ ∈ KO k D₂, ∀ X : Matrix A (D₁ ⊕ D₂) k,
      squareFlip μ σ ψ ν ϖ e (Assignment.one.block D₁ D₂) (fun Z => Φ (Z * fromBlocks M₁.val 0 0 M₂.val)) X =
        (ν (gdet M₁) : ℂ) * (((ν (gdet M₂))⁻¹ : ℂˣ) : ℂ) *
          squareFlip μ σ ψ ν ϖ e (Assignment.one.block D₁ D₂) Φ (X * fromBlocks M₁.val 0 0 M₂.val) := by
  intro k _ _ _ _ _ _ A A' D₁ D₂ _ _ _ _ _ _ _ _ μ hμ σ ψ ν ϖ e hϖ hψ he hν Φ hΦ M₁ hM₁ M₂ hM₂ X
  have h1 : fourierSum ψ ϖ e (Assignment.one.block D₁ D₂) (fun Z => Φ (Z * fromBlocks M₁.val 0 0 M₂.val)) =
      fun Y => fourierSum ψ ϖ e (Assignment.one.block D₁ D₂) Φ (Y * fromBlocks (invT M₁).val 0 0 M₂.val) :=
    funext (GlobalTheory.T.partialFourierSum_firstBlock_blockDiagonal ψ ϖ e hϖ hψ Φ hΦ M₁ hM₁ M₂ hM₂)
  have h2 : phiA μ σ ν ϖ e (blockLat ϖ e (Assignment.one.block D₁ D₂))
      (fun Y => fourierSum ψ ϖ e (Assignment.one.block D₁ D₂) Φ (Y * fromBlocks (invT M₁).val 0 0 M₂.val)) =
      ((ν (gdet M₁) : ℂ) * (((ν (gdet M₂))⁻¹ : ℂˣ) : ℂ)) • fun Z => phiA μ σ ν ϖ e
        (blockLat ϖ e (Assignment.one.block D₁ D₂)) (fourierSum ψ ϖ e (Assignment.one.block D₁ D₂) Φ)
          (Z * fromBlocks M₁.val 0 0 (invT M₂).val) :=
    funext fun Z => by
      rw [Pi.smul_apply, smul_eq_mul]
      exact @GlobalTheory.T.primitiveFrameDatum_blockSubstitution k _ _ _ _ _ _
        A A' D₁ D₂ _ _ _ _ _ _ _ _ μ hμ σ ν ϖ e _ M₁ hM₁ M₂ hM₂ Z
  have hd := GlobalTheory.FrameDepth.hasDepth_phiA (hμ := by assumption) k A A' (D₁ ⊕ D₂) μ σ ν ϖ e
    (blockUnits ϖ e (Assignment.one.block D₁ D₂)) _ hϖ he hν
    ((FourierDepth.fourier_exchange k A' (D₁ ⊕ D₂) ψ ϖ e _ hϖ hψ).1 Φ hΦ)
  have h3 : HasDepth ϖ e (blockLat ϖ e (Assignment.one.block D₁ D₂)ᶜ) (phiA μ σ ν ϖ e
      (blockLat ϖ e (Assignment.one.block D₁ D₂)) (fourierSum ψ ϖ e (Assignment.one.block D₁ D₂) Φ)) := by
    rw [← latA_blockLat]; exact hd
  unfold squareFlip
  rw [h1, h2, map_smul, Pi.smul_apply, smul_eq_mul,
    GlobalTheory.T.inversePartialFourierSum_comp_fromBlocks ψ⁻¹ ϖ e hϖ (hasConductor_inv hψ) _ h3 M₁ hM₁ M₂ hM₂ X]

end GlobalTheory.SquareFlipCols
end
end
