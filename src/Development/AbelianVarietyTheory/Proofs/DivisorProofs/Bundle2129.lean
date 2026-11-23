module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsFinWeil
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1775
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilDatumSplitSupportedEqIntertwinerMulHalfDetCh
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMixModelB
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsMixedLagrangianChartIntegralRowChange
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1780
import Formalism.LocalRingCardinality.ConjSqrtMinusD
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1282
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationLeOneOfMem
import Formalism.LocalRingCardinality.SpanPowerMembership.LocAtA
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUSplittingInl
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1045
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2091
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1185
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1051
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1115
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RatInOfUnit
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2039
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSelfDualOrientedModelConjugateHermitian
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsConstAlongSingleton
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2093
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
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1990
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1901
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardLatticeDoubleCosetClassesStabilisers
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2003
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite

@[expose] public section

section

open NumberField MeasureTheory IsDedekindDomain
open scoped Classical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 Hf lamOf area Th U)
open Formalism.MainNotions.StandardLatticesGL3 (WeilO HeckeU TT stdL pt oddE0)
open GlobalTheory.NormExact
open GlobalTheory.BotFormula (IsFinPt)
open GlobalTheory.BotClassDict (finQ)

attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.weilDatum_splitSupported_eq_intertwiner_mul_halfDetChar : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsStdChar D ψ (-1)) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle)
  (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om →
  ∀ (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)),
  IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ lam : ℕ →* ℂ, GlobalTheory.FinWeil.GoodNorm (GlobalTheory.FinWeil.sgO D) lam →
  (∀ n : ℕ, n ≠ 0 → (∀ q : ℕ, q.Prime → Formalism.MainNotions.StandardLatticesGL3.InertQ D q → ¬ q ∣ n) → lam n = (Real.sqrt n : ℂ)) →
  ∀ (w : 𝓞 D.host.E) (Om : GA D S × GA D T →* Module.End ℂ (GlobalTheory.FinWeilO.thetaSub ψ S T)),
  GlobalTheory.FinWeilO.IsLatRep hψ.1 ΛS ΛT w lam Om → ∀ ε : AE D, GlobalTheory.RatAut.IsHalfIdem D ε →
  ∀ (g : GA D S) (h : GA D T), SuppAt ε S g → SuppAt ε T h → ∀ x y : (AE D)ˣ, IsDetAt ε S g x → IsDetAt ε T h y →
  ∀ f : GlobalTheory.FinWeilO.thetaSub ψ S T,
    om (g, h) f = ((splitFacO χS χT x y : Circle) : ℂ) • (Om (g, h) f : WO S T → ℂ) := by
  first | exact @GlobalTheory.SplitWeilDict.splitWeil_eq | exact GlobalTheory.SplitWeilDict.splitWeil_eq | (intros; apply GlobalTheory.SplitWeilDict.splitWeil_eq <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta Formalism.L2.DIV IsDedekindDomain NumberField MeasureTheory Matrix
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop GlobalTheory.SqTower GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.ChainFr GlobalTheory.SquareDict GlobalTheory.SquareComm GlobalTheory.BigNZ GlobalTheory.FlipMatch GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA IsDatumB incM)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep Acts SInf At piW psiLoc chrW)
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopFlip

noncomputable section

namespace GlobalTheory.TopFlip.ChKO

section Lat

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem hatL_map {a b : ℕ} {Λ : Submodule (𝓞 E) (Fin a → E)} {Λ' : Submodule (𝓞 E) (Fin b → E)}
    (f : (Fin a → E ⊗[F] Formalism.L2.Herm.Af F) →ₗ[Formalism.L2.Herm.intAf F E] (Fin b → E ⊗[F] Formalism.L2.Herm.Af F))
    (hf : ∀ x ∈ Λ, ∃ y ∈ Λ', (fun i => Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F) (y i)) =
      f fun i => Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F) (x i)) :
    ∀ x ∈ Formalism.L2.Herm.hatL (F := F) Λ, f x ∈ Formalism.L2.Herm.hatL (F := F) Λ' := by
  intro x hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨x, hx, rfl⟩ := hx
    obtain ⟨y, hy, e⟩ := hf x hx
    exact Submodule.subset_span ⟨y, hy, e⟩
  | zero => rw [map_zero]; exact zero_mem _
  | add x z _ _ hx hz => rw [map_add]; exact add_mem hx hz
  | smul r x _ hx => rw [map_smul]; exact Submodule.smul_mem _ r hx


open GlobalTheory.Doubling in
theorem pairVec_mem_hatL {a b c : ℕ} (e : Fin a ⊕ Fin b ≃ Fin c) {Λ : Submodule (𝓞 E) (Fin a → E)}
    {Λ' : Submodule (𝓞 E) (Fin b → E)} (x : Fin a → E ⊗[F] Formalism.L2.Herm.Af F) (y : Fin b → E ⊗[F] Formalism.L2.Herm.Af F) :
    pairVec e x y ∈ Formalism.L2.Herm.hatL (F := F) (sumLat e Λ Λ') ↔
      x ∈ Formalism.L2.Herm.hatL (F := F) Λ ∧ y ∈ Formalism.L2.Herm.hatL (F := F) Λ' := by
  refine ⟨fun h => ⟨?_, ?_⟩, fun h => ?_⟩
  · have := hatL_map (Λ := sumLat e Λ Λ') (Λ' := Λ) (LinearMap.funLeft _ _ (e ∘ .inl)) (fun x hx => ⟨_, hx.1, rfl⟩) _ h
    convert this using 1
    funext i; simp [LinearMap.funLeft_apply]
  · have := hatL_map (Λ := sumLat e Λ Λ') (Λ' := Λ') (LinearMap.funLeft _ _ (e ∘ .inr)) (fun x hx => ⟨_, hx.2, rfl⟩) _ h
    convert this using 1
    funext i; simp [LinearMap.funLeft_apply]
  · let f₁ : (Fin a → E ⊗[F] Formalism.L2.Herm.Af F) →ₗ[Formalism.L2.Herm.intAf F E] (Fin c → E ⊗[F] Formalism.L2.Herm.Af F) :=
      { toFun := fun u => pairVec e u 0
        map_add' := fun u v => funext fun j => by obtain ⟨i | i, rfl⟩ := e.surjective j <;> simp
        map_smul' := fun r v => funext fun j => by obtain ⟨i | i, rfl⟩ := e.surjective j <;> simp }
    let f₂ : (Fin b → E ⊗[F] Formalism.L2.Herm.Af F) →ₗ[Formalism.L2.Herm.intAf F E] (Fin c → E ⊗[F] Formalism.L2.Herm.Af F) :=
      { toFun := fun u => pairVec e 0 u
        map_add' := fun u v => funext fun j => by obtain ⟨i | i, rfl⟩ := e.surjective j <;> simp
        map_smul' := fun r v => funext fun j => by obtain ⟨i | i, rfl⟩ := e.surjective j <;> simp }
    have h1 := hatL_map (Λ' := sumLat e Λ Λ') f₁ (fun u hu => ⟨pairVec e u 0, (pairVec_mem_sumLat e).2 ⟨hu, zero_mem _⟩,
      funext fun j => by obtain ⟨i | i, rfl⟩ := e.surjective j <;> simp [f₁]⟩) _ h.1
    have h2 := hatL_map (Λ' := sumLat e Λ Λ') f₂ (fun u hu => ⟨pairVec e 0 u, (pairVec_mem_sumLat e).2 ⟨zero_mem _, hu⟩,
      funext fun j => by obtain ⟨i | i, rfl⟩ := e.surjective j <;> simp [f₂]⟩) _ h.2
    convert add_mem h1 h2 using 1
    funext j
    obtain ⟨i | i, rfl⟩ := e.surjective j <;> simp [f₁, f₂]


open GlobalTheory.Doubling in
theorem isFrame_blkGL {a b c : ℕ} (e : Fin a ⊕ Fin b ≃ Fin c) {Λ : Submodule (𝓞 E) (Fin a → E)}
    {Λ' : Submodule (𝓞 E) (Fin b → E)} {β : GL (Fin a) (E ⊗[F] Formalism.L2.Herm.Af F)} {β' : GL (Fin b) (E ⊗[F] Formalism.L2.Herm.Af F)}
    (h : IsFrame β Λ) (h' : IsFrame β' Λ') : IsFrame (blkGL e (β, β')) (sumLat e Λ Λ') := by
  intro x
  rw [← pairVec_eta e x, pairVec_mem_hatL, h, h']
  change _ ↔ ∀ i, (blkMat e (β⁻¹).val (β'⁻¹).val *ᵥ _) i ∈ _
  rw [blkMat_mulVec]
  refine ⟨fun H j => ?_, fun H => ⟨fun i => ?_, fun i => ?_⟩⟩
  · obtain ⟨i | i, rfl⟩ := e.surjective j
    · rw [pairVec_inl]; exact H.1 i
    · rw [pairVec_inr]; exact H.2 i
  · have := H (e (.inl i)); rwa [pairVec_inl] at this
  · have := H (e (.inr i)); rwa [pairVec_inr] at this

theorem isFrame_neg {a : ℕ} {Λ : Submodule (𝓞 E) (Fin a → E)} {β : GL (Fin a) (E ⊗[F] Formalism.L2.Herm.Af F)}
    (h : IsFrame β Λ) : IsFrame (-β) Λ := by
  intro x
  rw [h, inv_neg, Units.val_neg, neg_mulVec]
  exact forall_congr' fun i => neg_mem_iff.symm

theorem int_change {a : ℕ} {Λ : Submodule (𝓞 E) (Fin a → E)} {β β' : GL (Fin a) (E ⊗[F] Formalism.L2.Herm.Af F)}
    (h : IsFrame β Λ) (h' : IsFrame β' Λ) (i j : Fin a) : (β'⁻¹ * β).val i j ∈ Formalism.L2.Herm.intAf F E := by
  have h1 := (h (β.val *ᵥ Pi.single j 1)).2 fun l => by
    rw [mulVec_mulVec, Units.inv_mul, one_mulVec, Pi.single_apply]
    split_ifs
    exacts [one_mem _, zero_mem _]
  have h2 := (h' _).1 h1 i
  rwa [mulVec_mulVec, mulVec_single_one] at h2

end Lat

variable {D : D7}

theorem isEquiv_val (w : Pl D.host.E) :
    (ValuativeRel.valuation (Kw w)).IsEquiv (Valued.v : Valuation (Kw w) (WithZero (Multiplicative ℤ))) :=
  haveI : (Valued.v : Valuation (Kw w) (WithZero (Multiplicative ℤ))).Compatible := Valuation.Compatible.ofValuation _
  ValuativeRel.isEquiv _ _

theorem change_mem_KO {a : ℕ} {Λ : Submodule (𝓞 D.host.E) (Fin a → D.host.E)} {β β' : GL (Fin a) (Formalism.IndefR.Lev.EAf D)}
    (h : IsFrame β Λ) (h' : IsFrame β' Λ) (w : Pl D.host.E) : (loc w β')⁻¹ * loc w β ∈ KO (Kw w) (Fin a) := by
  have key : ∀ {β β' : GL (Fin a) (Formalism.IndefR.Lev.EAf D)}, IsFrame β Λ → IsFrame β' Λ → ∀ i j,
      ((loc w β')⁻¹ * loc w β).val i j ∈ (ValuativeRel.valuation (Kw w)).integer := fun {β β'} h h' i j => by
    have h2 := (mem_OA_iff _).1 (int_change h h' i j) w
    rw [← map_inv, ← map_mul]
    exact (isEquiv_val w).le_one_iff_le_one.2 h2
  refine (mem_KO_iff _).2 ⟨key h h', ?_⟩
  rw [_root_.mul_inv_rev, inv_inv]
  exact key h' h

theorem reGL_mem_KO {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] (e : a ≃ b) {g : GL a k} (hg : g ∈ KO k a) :
    GlobalTheory.StepData.reGL e g ∈ KO k b := by
  obtain ⟨h1, h2⟩ := (mem_KO_iff _).1 hg
  refine (mem_KO_iff _).2 ⟨fun i j => h1 _ _, fun i j => ?_⟩
  rw [← map_inv]
  exact h2 _ _

theorem scalar_mem_KO {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {a : Type} [Fintype a] [DecidableEq a] (u : kˣ) (hu : ValuativeRel.valuation k u = 1) :
    Units.map (Matrix.scalar a).toMonoidHom u ∈ KO k a := by
  have key : ∀ u : kˣ, ValuativeRel.valuation k u = 1 → ∀ i j,
      (Units.map (Matrix.scalar a).toMonoidHom u).val i j ∈ (ValuativeRel.valuation k).integer := fun u hu i j => by
    change Matrix.diagonal (fun _ => (u : k)) i j ∈ _
    rw [diagonal_apply]
    split_ifs
    exacts [hu.le, zero_mem _]
  refine (mem_KO_iff _).2 ⟨key u hu, ?_⟩
  rw [← map_inv]
  exact key _ (by rw [Units.val_inv_eq_inv_val, map_inv₀, hu, inv_one])

theorem val_xiAt (w : Pl D.host.E)
    (hw : ((D.host.QS * D.host.q * D.host.d * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal) :
    ValuativeRel.valuation (Kw w) (xiAt w) = 1 := by
  have hn : ∀ n : ℕ, n ∣ D.host.QS * D.host.q * D.host.d * Ideal.absNorm D.host.ccK → w.valuation D.host.E (n : D.host.E) = 1 := by
    rintro n ⟨m, hm⟩
    have : (n : 𝓞 D.host.E) ∉ w.asIdeal := fun h => hw (by rw [hm, Nat.cast_mul]; exact Ideal.mul_mem_right _ _ h)
    have := (w.valuation_eq_one_iff_notMem (K := D.host.E)).2 this
    rwa [map_natCast] at this
  have h1 := hn _ (dvd_mul_left _ _)
  have h2 := hn D.host.d (Dvd.dvd.mul_right (dvd_mul_left _ _) _)
  have h3 : w.valuation D.host.E D.host.sqrtMinusD = 1 := by
    have := congrArg (w.valuation D.host.E) D.host.sqrtMinusD_sq
    rw [map_pow, Valuation.map_neg, h2] at this
    exact (pow_eq_one_iff_of_nonneg zero_le' two_ne_zero).1 this
  have h4 : w.valuation D.host.E D.host.xi0 = 1 := by
    unfold Formalism.BasicNotions.Host.xi0
    rw [map_div₀, map_mul, h1, h3, Valuation.map_neg, map_one, mul_one, div_one]
  refine (isEquiv_val w).eq_one_iff_eq_one.2 ?_
  exact (w.valuedAdicCompletion_eq_valuation' _).trans h4

theorem changes_mem_KO : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GridData L sc} {μ₀ : T}, L.Is μ₀ → ∀ (B : Frames G) (t : T) (i j : Fin D.R.m) (X : TriG G i j), SquareStanding G t →
      IsFrame X.rA.β (G.Λ (.grid (i + 1) (j + 1))) → IsFrame X.rA'.β (G.Λ (.grid i j)) → IsFrame X.rW.β (latX G i j) →
      ∀ w ∈ locPl G t, chA B t X w ∈ KO (Kw w) _ ∧ chB B t X w ∈ KO (Kw w) _ ∧ chX B t X w ∈ KO (Kw w) _ := by
  intro D T L sc G μ₀ hL B t i j X hS hA hA' hW w hw
  refine ⟨reGL_mem_KO _ (invT_mem_KO (change_mem_KO (B.isFrame_β hL i.2 j.2) hA w)),
    reGL_mem_KO _ (mul_mem (scalar_mem_KO _ (val_xiAt w (hS.2 w hw))) (change_mem_KO (B.isFrame_β hL i.2.le j.2.le) hA' w)),
    reGL_mem_KO _ (change_mem_KO hW (isFrame_blkGL finSumFinEquiv (B.isFrame_β hL i.2.le j.2)
      (isFrame_neg (B.isFrame_β hL i.2 j.2.le))) w)⟩

end GlobalTheory.TopFlip.ChKO

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta Formalism.L2.DIV IsDedekindDomain NumberField MeasureTheory Matrix
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop GlobalTheory.SqTower GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.ChainFr GlobalTheory.SquareDict GlobalTheory.SquareComm GlobalTheory.BigNZ GlobalTheory.FlipMatch GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA IsDatumB incM)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep Acts SInf At piW psiLoc chrW)
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopFlip

noncomputable section

namespace GlobalTheory.TopFlip.ChartA

open GlobalTheory.FlipMatch.RowChart GlobalTheory.LFun GlobalTheory.LFun.SplitTie
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (blk)

theorem tr_full {k : Type} [Field k] {n p q d : ℕ} (e : Fin p ⊕ Fin q ≃ Fin d) {b β g : GL (Fin n) k}
    {Gm : Matrix (Fin n) (Fin n) k} (hg : g.val = -(β.valᵀ * Gmᵀ * b.val))
    {c cc : GL (Fin d) k} {βV : GL (Fin p) k} {β₁ : GL (Fin q) k} (hC : c.val * cc.val = blk e βV.val (-β₁.val))
    (U : Matrix (Fin n) (Fin d) k) :
    g.val * ((b⁻¹).val * U * (c⁻¹).valᵀ) * (invT cc).val =
      (blk e (βV⁻¹).val (-(β₁⁻¹).val) * (Uᵀ * -Gm) * β.val)ᵀ := by
  have h : g.val * ((b⁻¹).val * U * (c⁻¹).valᵀ) * (invT cc).val =
      (-(β.valᵀ * Gmᵀ) * U) * blk e (βV⁻¹).valᵀ (-(β₁⁻¹).valᵀ) := by
    rw [← inv_of_blk e hC, invT_val, hg]
    simp only [Matrix.neg_mul, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc b.val, Units.mul_inv, Matrix.one_mul]
  rw [h]
  simp only [transpose_mul, transpose_neg, transpose_transpose, Matrix.neg_mul, Matrix.mul_neg, Matrix.mul_assoc,
    GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk_transpose]

theorem map_frame {A R k : Type} [CommRing A] [CommRing R] [Field k] (f : A →+* R) (c : R →+* k) {n p q d : ℕ}
    (e : Fin p ⊕ Fin q ≃ Fin d) (β : GL (Fin n) R) (βV : GL (Fin p) R) (β₁ : GL (Fin q) R)
    (J : Matrix (Fin n) (Fin n) A) (u : Matrix (Fin n) (Fin d) A) :
    (((GlobalTheory.Doubling.blkGL finSumFinEquiv (βV, -β₁))⁻¹).val *
        (uᵀ.submatrix (e.symm.trans finSumFinEquiv).symm id * J).map f * β.val).map c =
      (blk e ((GeneralLinearGroup.map c βV)⁻¹).val (-((GeneralLinearGroup.map c β₁)⁻¹).val) *
        ((u.map (c.comp f))ᵀ * J.map (c.comp f)) * (GeneralLinearGroup.map c β).val).submatrix
        (e.symm.trans finSumFinEquiv).symm id := by
  have h1 : (((GlobalTheory.Doubling.blkGL finSumFinEquiv (βV, -β₁))⁻¹).val).map c =
      (blk e ((GeneralLinearGroup.map c βV)⁻¹).val (-((GeneralLinearGroup.map c β₁)⁻¹).val)).submatrix
        (e.symm.trans finSumFinEquiv).symm (e.symm.trans finSumFinEquiv).symm := by
    have h0 : ((GlobalTheory.Doubling.blkGL finSumFinEquiv (βV, -β₁))⁻¹).val =
        GlobalTheory.Doubling.blkMat finSumFinEquiv (βV⁻¹).val (-(β₁⁻¹).val) := rfl
    rw [h0, GlobalTheory.Doubling.blkMat_map _ _ (map_zero c), Matrix.map_neg _ (map_neg c)]
    ext a b
    simp only [GlobalTheory.Doubling.blkMat, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk, submatrix_apply, reindex_apply, Equiv.symm_trans_apply, Equiv.symm_symm,
      Equiv.symm_apply_apply]
    rfl
  rw [Matrix.map_mul, Matrix.map_mul, h1, Matrix.map_mul, Matrix.map_mul]
  have h2 : ((uᵀ.submatrix (e.symm.trans finSumFinEquiv).symm id).map f).map c * (J.map f).map c =
      ((u.map (c.comp f))ᵀ * J.map (c.comp f)).submatrix (e.symm.trans finSumFinEquiv).symm id := rfl
  rw [h2, submatrix_mul_equiv]
  rfl

section Grid

variable {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GridData L sc} (B : Frames G) (t : T)
  (i j : Fin D.R.m) (e : Num G i j)

theorem linA_ptA (w : Pl D.host.E)
    (u : Matrix (Fin (spW G i j).rank) (Fin ((spW G i j).rank + (spW₁ G i j).rank)) (AE D)) :
    linA B t i j w (ptA e u) = reindex (finCongr (rankW G t i j w)) (colsEq t e w)
      (blk e ((loc w (B.β i (j + 1)))⁻¹).val (-((loc w (B.β (i + 1) j))⁻¹).val) *
        HMul.hMul (u.map (cw w))ᵀ (-(spW G i j).gram.map (algebraMap D.host.E (Kw w))) *
        (loc w (B.β (i + 1) (j + 1))).val)ᵀ := by
  have eJ : (incM (GlobalTheory.Grid.sgn true (spW G i j)).gram).map (cw w) =
      -(spW G i j).gram.map (algebraMap D.host.E (Kw w)) :=
    Matrix.ext fun a b => (Good.cpt_incA _ _).trans (map_neg (algebraMap D.host.E (Kw w)) _)
  have k2 := map_frame (toEAf D) (cpt (D := D) w) (n := (spW G i j).rank) e (B.β (i + 1) (j + 1)) (B.β i (j + 1))
    (B.β (i + 1) j) (incM (GlobalTheory.Grid.sgn true (spW G i j)).gram) u
  rw [← eJ]
  refine Matrix.ext fun r s => ?_
  refine (congrFun (congrFun k2 ((colX G t i j w).symm s)) ((finCongr (rankW G t i j w)).symm r)).trans ?_
  have hs : (e.symm.trans finSumFinEquiv).symm ((colX G t i j w).symm s) = (colsEq t e w).symm s :=
    congrArg e (finSumFinEquiv.symm_apply_apply _)
  rw [submatrix_apply, hs]
  rfl

theorem chart_eq_linA (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j) {v : Pl D.host.F}
    (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v) (w : Pl D.host.E) (ψ : Fv D.host.F v ≃+* Kw w) (hjj : IsPlaceIso τ w ψ)
    (cc : GL (Fin ((spW G i j).rank + (spW₁ G i j).rank)) (Kw w))
    (hcc : (Γ.W.bas v).val.map ψ * cc.val = basCols B e w) (g : GL (Fin (spW G i j).rank) (Kw w))
    (hg : g.val = -((loc w (B.β (i + 1) (j + 1))).valᵀ *
      ((spW G i j).gram.map (algebraMap D.host.E (Kw w)))ᵀ * (Γ.V.bas v).val.map ψ))
    (u : Matrix (Fin (spW G i j).rank) (Fin ((spW G i j).rank + (spW₁ G i j).rank)) (AE D)) :
    chart ψ (finCongr (rankW G t i j w)) (colsEq t e w) g (invT cc) (coX τ (Γ.V.bas v) (Γ.W.bas v) u) =
      linA B t i j w (ptA e u) := by
  have eU : (u.map (piW τ)).map ψ = u.map (cw w) := Matrix.ext fun a b => hjj _
  have k1 := tr_full e (b := GeneralLinearGroup.map ψ.toRingHom (Γ.V.bas v))
    (c := GeneralLinearGroup.map ψ.toRingHom (Γ.W.bas v)) (β := loc w (B.β (i + 1) (j + 1)))
    (βV := loc w (B.β i (j + 1))) (β₁ := loc w (B.β (i + 1) j)) hg hcc (u.map (cw w))
  rw [linA_ptA, chart, chart_coX, eU]
  exact congrArg _ k1

end Grid

theorem exists_mixChart_lin : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GridData L sc} {μ₀ : T}, L.Is μ₀ → ∀ (W : G.Weil) (B : Frames G) (t : T) (i j : Fin D.R.m) (M : Vol G), SquareStanding G t →
    ∀ (e : Num G i j) (Bs : Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j) (X : Chars D.host.F D.host.E)
      (om : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W) (om' : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W), IsTripleOf W M t i j e Bs Γ X →
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ X om om' → IsTied t i j e Bs Γ X →
    ∀ (v : Bs.P) (w : Pl D.host.E), splitPrime (Bs.τ v) = w → ∀ jj : Fv D.host.F v ≃+* Kw w, IsPlaceIso (Bs.τ v) w jj → IsLocIso jj →
    ∀ cc : GL (Fin ((spW G i j).rank + (spW₁ G i j).rank)) (Kw w), (Γ.W.bas v).val.map jj * cc.val = basCols B e w →
    ∃ g ∈ KO (Kw w) (Fin (spW G i j).rank),
      IsMixChart v.1 (mixHalf e (atPl w 1)) (mixHalf e (cA D (atPl w 1))) (mixCo B t e w)
        (fun u => chart jj (finCongr (rankW G t i j w)) (colsEq t e w) g (invT cc) (coX (Bs.τ v) (Γ.V.bas v) (Γ.W.bas v) u))
        (fun u => (xiAt w)⁻¹ • chart jj (finCongr (rankW G t i j w)) (colsEq t e w) (invT g) cc
          (coY D.sp.cm.sig Γ.V Γ.W (Bs.τ v) (Γ.V.bas v) (Γ.W.bas v) u))
        (Assignment.one.block _ _)ᶜ ∧
      ∀ u, chart jj (finCongr (rankW G t i j w)) (colsEq t e w) g (invT cc) (coX (Bs.τ v) (Γ.V.bas v) (Γ.W.bas v) u) =
        linA B t i j w (ptA e u) := by
  classical
  intro D T L sc G μ₀ hL W B t i j M _ e Bs Γ X om om' h hT hTi v w hw jj hjj _ cc hcc
  subst hw
  obtain rfl := eq_complEquiv _ hjj
  have hV := hT.geo.hV
  have hJT : IsHermND D.sp.cm.sig Γ.V.Jᵀ := ⟨fun i j => by simpa using hV.herm j i, by
    rw [Matrix.det_transpose]; exact GlobalTheory.HermSelfDualLoc.det_ne_zero_of_isHerm _ Bs hV⟩
  have hsd := GlobalTheory.HermSelfDualLoc.isSelfDualAt_transpose _ _ _ Bs _ Γ.V _ _ hT.base hV v
  have hb := hV.bas v
  rw [hTi.1] at hsd hb
  obtain ⟨g, hgK, hg⟩ := exists_rows (Bs.τ v) hJT hsd hb
    (isFrameAt_loc (B.isFrame_β hL (i := (i : ℕ) + 1) (j := (j : ℕ) + 1) i.2 j.2) (splitPrime (Bs.τ v)))
  have hJW : Γ.V.J = (spW G i j).gram := h.JW.trans (one_smul _ _)
  rw [hJW] at hg
  refine ⟨g, hgK, isMixChart_of B t i j e Γ (Bs.τ v) _ hjj (complMap_apply_emb _ _) hJW h.JWW cc hcc g hg, fun u => ?_⟩
  exact chart_eq_linA B t i j e Γ (Bs.τ v) _ _ hjj cc hcc g hg u

end GlobalTheory.TopFlip.ChartA

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical


theorem _root_.GlobalTheory.T.exists_local_finiteDim_finiteParts_weilOperators : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (S T : HSp D) (χS χT : (AE D)ˣ →* Circle), IsHeckeChar D χS → IsHeckeChar D χT →
      ResEta D χS S.rank → ResEta D χT T.rank →
      ∀ (JA : Matrix (Fin T.rank) (Fin T.rank) D.host.E) (JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E)
        (ξ : AF D.host.F ⊗[D.host.F] D.host.E), JA = T.gramᵀ →
        ξ • incM D.host.F JB = incM D.host.F (D.host.xi0 • S.gram⁻¹) →
        ∀ (κ : Type) [Fintype κ]
          (co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ (incM D.host.F JA) (incM D.host.F JB)) κ),
          (∀ x : Matrix (Fin T.rank) (Fin S.rank) D.host.E, ∃ y z : κ → D.host.F,
            co.e (incM D.host.F x) = (fun i => algebraMap D.host.F (AF D.host.F) (y i), fun i => algebraMap D.host.F (AF D.host.F) (z i))) →
          ∀ ω : GA D S × GA D T →* Module.End ℂ (Formalism.IndefR.Datum.WO S T → ℂ),
            Formalism.IndefR.Datum.IsWeilDatumO ψ S T χS χT ω →
 ∀ om : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JA) ×
      GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JB) →* Module.End ℂ ((κ → AF D.host.F) → ℂ),
                       GlobalTheory.WeilSchrodinger.IsTransport ψ co ω om →
  ∀ Φ ∈ GlobalTheory.WeilM.schA D.host.F κ, ∀ p0, ∃ N ∈ nhds p0, ∃ (m : ℕ) (g : Fin m → (κ → FiniteAdeleRing (𝓞 D.host.F) D.host.F) → ℂ)
      (y : Fin m → κ → FiniteAdeleRing (𝓞 D.host.F) D.host.F),
      (∀ i, g i ∈ GlobalTheory.WeilM.SB (κ → FiniteAdeleRing (𝓞 D.host.F) D.host.F)) ∧ (∀ i j, g i (y j) = if i = j then 1 else 0) ∧
      ∀ p ∈ N, ∃ f : Fin m → SchwartzMap (κ → mixedEmbedding.mixedSpace D.host.F) ℂ,
        om p Φ = ∑ i, GlobalTheory.WeilM.pureA D.host.F (f i) (g i) := by
  first | exact @GlobalTheory.WeilCont.exists_local_finite_parts | exact GlobalTheory.WeilCont.exists_local_finite_parts | (intros; apply GlobalTheory.WeilCont.exists_local_finite_parts <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.EndOnTorsion
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DoubleClassExtension

theorem two_smul_extends : ∀ (S : Scheme.{0}) [IsIntegral S] [IsLocallyNoetherian S], ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme S → ∀ (A : Over S) [GrpObj A], IsAbelianScheme A → ∀ (U : S.Opens) (V : A.left.Opens), (U : Set S).Nonempty → (∀ s : S, ∃ x ∈ V, A.hom x = s) → ∀ c : Pic (A.hom ⁻¹ᵁ U ⊔ V).toScheme, GlobalTheory.CechPic.pull (A.left.homOfLE (le_sup_right : V ≤ A.hom ⁻¹ᵁ U ⊔ V)) c = 0 → ∃ c' : Pic A.left, GlobalTheory.CechPic.pull (A.hom ⁻¹ᵁ U ⊔ V).ι c' = 2 • c := by
  intro S _ _ hS A _ hA U V hU hV c hc
  haveI : Smooth A.hom := hA.smooth
  haveI : GeometricallyConnected A.hom := hA.geomConnected
  haveI : GeometricallyIntegral A.hom := GlobalTheory.geometricallyIntegral_of_smooth A.hom
  haveI : GlobalTheory.IsNormalScheme S := GlobalTheory.IsNormalScheme.of_pred hS
  haveI : GlobalTheory.IsNormalScheme A.left := GlobalTheory.isNormalScheme_of_smooth A.hom
  haveI : IsLocallyNoetherian A.left := LocallyOfFiniteType.isLocallyNoetherian A.hom
  have hbig := GlobalTheory.T.mem_preimage_sup_of_stalk_krullDim_le_one_flat A.left S A.hom V U hV hU
  obtain ⟨Y, x, a, v, p, e, _, hxs, hxsurj, hpv, hmem, hsm2, hgi2, he⟩ := GlobalTheory.T.exists_parameterScheme_triples_abelianScheme S A hA V hV
  haveI := hxs
  haveI := hxsurj
  have h2 := GlobalTheory.T.cechPicard_two_nsmul_pullback_eq_zero_on_tripleParameterScheme S hS A hA U V (A.hom ⁻¹ᵁ U ⊔ V) le_sup_right hU hV le_sup_left le_rfl c hc
    Y x a v p e hpv hmem hsm2 hgi2 he
  haveI : GlobalTheory.IsNormalScheme Y.left := GlobalTheory.isNormalScheme_of_smooth x.left
  have hbigY := GlobalTheory.T.flat_preimage_contains_codim_le_one_points A.left Y.left x.left _ hbig
  have hloc := GlobalTheory.T.picardClass_locally_trivial_of_trivial_smooth_normal_cover A.left Y.left x.left (GlobalTheory.IsNormalScheme.pred _) _ hbigY (2 • c) h2
  exact GlobalTheory.T.cechPicard_extend_of_locally_trivial_normal_codimTwo A.left (GlobalTheory.IsNormalScheme.pred _) _ hbig (2 • c) hloc

end GlobalTheory.DoubleClassExtension
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.exists_selfDual_orientedModel_conjugate_hermitian : ∀ (D : D7) (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E), Bs.IsGood D.sp.cm.sig → GlobalTheory.SqStepBig.EmbCM Bs →
    ∀ (n r p : ℕ) (V : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E n), V.IsHerm D.sp.cm.sig Bs r p →
      ∃ (B : HSp D) (Λ : Submodule (𝓞 D.host.E) (Fin B.rank → D.host.E)),
        IsSelfDualC B Λ ∧ NegIdx B p ∧ GlobalTheory.SqStepBig.OverH 1 B Λ V := by
  first | exact @GlobalTheory.ConjSpace.main | exact GlobalTheory.ConjSpace.main | (intros; apply GlobalTheory.ConjSpace.main <;> assumption)
end

section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet
open scoped TensorProduct

theorem _root_.GlobalTheory.T.hermitianWittFrame_unipotent_le_flag_unipotent : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E), IsWittFrame σ J X Y → ∀ (S : Finset (Fin r)) (s : ℕ) (hs : s ≤ r), (∀ i : Fin r, i.val < s ↔ ∃ k ∈ S, i ≤ k) → ∀ d : Fin s → ℕ, (∀ i, d i = (S.filter (· < Fin.castLE hs i)).card) → GlobalTheory.StdPar.unip σ J X S ≤ GlobalTheory.UAut.unipFlag σ J (X.submatrix id (Fin.castLE hs)) d := by
  first | exact @GlobalTheory.TieStd.unip_le_unipFlag | exact GlobalTheory.TieStd.unip_le_unipFlag | (intros; apply GlobalTheory.TieStd.unip_le_unipFlag <;> assumption)
end
