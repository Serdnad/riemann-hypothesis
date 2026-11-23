module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2426
public import ReciprocityTheory.ReductiveGroups.LatticeEmbeddings.Bundle001
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle048
public import Formalism.LocalRingCardinality.SpanPowerMembership.Bundle007
import Formalism.LocalRingCardinality.SpanPowerMembership.Bundle005
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2438
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle016
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsIsScalar
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ToUnitsCompToCircle
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle026
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle652
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle923
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle856
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2443
public import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.CoefFnEqZeroOfNotPos
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle095
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle063
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ChartIndependenceUnconditional
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle025
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUSplittingInl
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle265
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2446
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
import Mathlib.RingTheory.Valuation.Integral
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
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Topology.Separation.CompletelyRegular
import ReciprocityTheory.Automorphisms.PlaceA
import Development.AbelianVarietyTheory.Definitions.Divisors.LevelOfOfSameBut
import Development.AbelianVarietyTheory.Definitions.Divisors.TupleReadBaseTupleEqFamily
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle017
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle059
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
import Development.AbelianVarietyTheory.Definitions.ThetaValues.Bundle002
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain
open scoped TensorProduct

namespace GlobalTheory.EvExtend

variable {F : Type} [Field F] [NumberField F] {l : ℕ} [Fact l.Prime]

theorem norm_natCast_lt_one : ‖((l : ℕ) : PadicAlgCl l)‖ < 1 := by
  have h := PadicComplex.norm_extends l ((l : ℕ) : PadicAlgCl l)
  rw [← h]
  simpa using ReciprocityTheory.ChartRestriction.B3.IotaPl.norm_p_lt_one (p := l)

omit [NumberField F] in
theorem norm_int_le_one (φ : F →+* PadicAlgCl l) (y : 𝓞 F) : ‖φ (y : F)‖ ≤ 1 := by
  have hi : IsIntegral ℤ (φ (y : F)) := (RingOfIntegers.isIntegral_coe y).map φ.toIntAlgHom
  have h2 := (Valuation.integer.integers (NormedField.valuation (K := PadicAlgCl l))).isIntegral_iff_v_le_one.mp
    hi.tower_top
  exact_mod_cast (show ‖φ (y : F)‖₊ ≤ 1 from h2)

def placeOf (φ : F →+* PadicAlgCl l) : HeightOneSpectrum (𝓞 F) where
  asIdeal := ReciprocityTheory.ChartRestriction.B3.IotaPl.smallIdeal ((algebraMap (PadicAlgCl l) ℂ_[l]).comp φ)
  isPrime := ReciprocityTheory.ChartRestriction.B3.IotaPl.smallIdeal_isPrime _
  ne_bot := by
    intro h
    have hm : ((l : ℕ) : 𝓞 F) ∈ ReciprocityTheory.ChartRestriction.B3.IotaPl.smallIdeal ((algebraMap (PadicAlgCl l) ℂ_[l]).comp φ) := by
      rw [ReciprocityTheory.ChartRestriction.B3.IotaPl.mem_smallIdeal]
      simpa using ReciprocityTheory.ChartRestriction.B3.IotaPl.norm_p_lt_one (p := l)
    rw [h, Submodule.mem_bot] at hm
    exact (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero) hm

theorem mem_placeOf (φ : F →+* PadicAlgCl l) (x : 𝓞 F) : x ∈ (placeOf φ).asIdeal ↔ ‖φ (x : F)‖ < 1 := by
  show ‖(algebraMap (PadicAlgCl l) ℂ_[l]) (φ (x : F))‖ < 1 ↔ _
  rw [show ‖(algebraMap (PadicAlgCl l) ℂ_[l]) (φ (x : F))‖ = ‖φ (x : F)‖ from PadicComplex.norm_extends _ _]

theorem norm_le_one_iff (φ : F →+* PadicAlgCl l) (x : F) : ‖φ x‖ ≤ 1 ↔ (placeOf φ).valuation F x ≤ 1 :=
  Formalism.BasicNotions.Examples₂.norm_le_one_iff_val φ (placeOf φ) (norm_int_le_one φ) (mem_placeOf φ) x

theorem val_lt_one_iff (φ : F →+* PadicAlgCl l) (x : F) : (placeOf φ).valuation F x < 1 ↔ ‖φ x‖ < 1 := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  have h := norm_le_one_iff φ x⁻¹
  have hpos : 0 < ‖φ x‖ := norm_pos_iff.2 ((map_ne_zero φ).2 hx)
  have hv : 0 < (placeOf φ).valuation F x := by
    rw [pos_iff_ne_zero]; exact (Valuation.ne_zero_iff _).2 hx
  rw [map_inv₀, norm_inv, inv_le_one₀ hpos, map_inv₀, inv_le_one₀ hv] at h
  rw [← not_le, ← not_le, h]

end GlobalTheory.EvExtend

namespace GlobalTheory.EvExtend

variable {F : Type} [Field F] [NumberField F] {l : ℕ} [Fact l.Prime]

theorem exists_ext (φ : F →+* PadicAlgCl l) :
    ∃ j : (placeOf φ).adicCompletion F →+* PadicAlgCl l, Continuous j ∧
      (∀ x : F, j (algebraMap F _ x) = φ x) ∧
      (∀ y ∈ (placeOf φ).adicCompletionIntegers F, ‖j y‖ ≤ 1) ∧
      ∀ (K : IntermediateField ℚ_[l] (PadicAlgCl l)), FiniteDimensional ℚ_[l] K → (∀ x, φ x ∈ K) → ∀ y, j y ∈ K := by
  obtain ⟨j, hjc, hj⟩ := GlobalTheory.exists_continuous_extension_adicCompletion F l φ (placeOf φ) (val_lt_one_iff φ)
  have hj' : ∀ x : F, j (algebraMap F _ x) = φ x := fun x => RingHom.congr_fun hj x
  have hd := HeightOneSpectrum.denseRange_algebraMap F (placeOf φ)
  refine ⟨j, hjc, hj', fun y hy => ?_, fun K hK hφK y => ?_⟩
  · have hO : IsOpen (((placeOf φ).adicCompletionIntegers F : Set ((placeOf φ).adicCompletion F))) :=
      Valued.isOpen_valuationSubring _
    have hcl : IsClosed {y : (placeOf φ).adicCompletion F | ‖j y‖ ≤ 1} :=
      isClosed_le (continuous_norm.comp hjc) continuous_const
    refine closure_minimal ?_ hcl (hd.open_subset_closure_inter hO hy)
    rintro _ ⟨hy1, x, rfl⟩
    show ‖j (algebraMap F _ x)‖ ≤ 1
    rw [hj', norm_le_one_iff]
    rw [SetLike.mem_coe, HeightOneSpectrum.mem_adicCompletionIntegers, ReciprocityTheory.Aut.adic_valued_algebraMap] at hy1
    exact hy1
  · have : CompleteSpace K := FiniteDimensional.completeSpace ℚ_[l] K
    have hKc : IsClosed (K : Set (PadicAlgCl l)) := (completeSpace_coe_iff_isComplete.mp ‹_›).isClosed
    exact hd.induction_on (p := fun y => j y ∈ K) y (hKc.preimage hjc) fun x => by
      show j (algebraMap F _ x) ∈ K
      rw [hj']; exact hφK x

end GlobalTheory.EvExtend

namespace GlobalTheory.EvExtend

theorem exists_evOk : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (l : ℕ) [Fact l.Prime]
    (i : E →+* PadicAlgCl l), ∃ ev : FiniteAdeleRing (𝓞 F) F ⊗[F] E →+* PadicAlgCl l, GlobalTheory.FrameOf.EvOk i ev := by
  intro F E _ _ _ _ _ l _ i
  let φ : F →+* PadicAlgCl l := i.comp (algebraMap F E)
  obtain ⟨j, -, hj, hint, hK⟩ := exists_ext φ
  let v := placeOf φ
  let e0 : FiniteAdeleRing (𝓞 F) F →+* v.adicCompletion F :=
    { toFun := fun a => a v, map_one' := rfl, map_mul' := fun _ _ => rfl, map_zero' := rfl,
      map_add' := fun _ _ => rfl }
  let : Algebra F (PadicAlgCl l) := φ.toAlgebra
  let f : FiniteAdeleRing (𝓞 F) F →ₐ[F] PadicAlgCl l :=
    { j.comp e0 with commutes' := fun x => hj x }
  let g : E →ₐ[F] PadicAlgCl l := { i with commutes' := fun x => rfl }
  let ev : FiniteAdeleRing (𝓞 F) F ⊗[F] E →+* PadicAlgCl l :=
    (Algebra.TensorProduct.lift f g fun _ _ => Commute.all _ _).toRingHom
  have hev : ∀ a e, ev (a ⊗ₜ[F] e) = j (a v) * i e := fun a e => Algebra.TensorProduct.lift_tmul _ _ _ _ _
  refine ⟨ev, fun x => ?_, fun a ha => ?_, fun a ha => ?_, fun y => ?_⟩
  · rw [hev]
    show j 1 * i x = i x
    rw [map_one, one_mul]
  · rw [hev, map_one, mul_one]
    exact hint _ (ha v)
  · have hl : ((l : ℕ) : 𝓞 F) ∈ v.asIdeal := by
      rw [mem_placeOf]
      simpa [φ] using norm_natCast_lt_one (l := l)
    rw [hev, ha v hl, map_zero, zero_mul]
  · have hKle : Formalism.BasicNotions.Examples₂.LB.Kphi i ≤ IntermediateField.adjoin ℚ_[l] (Set.range i) :=
      IntermediateField.adjoin.mono _ _ _ (by rintro _ ⟨k, rfl⟩; exact ⟨_, rfl⟩)
    have hmem : ∀ a e, ev (a ⊗ₜ[F] e) ∈ Formalism.BasicNotions.Examples₂.LB.Kphi i := fun a e => by
      rw [hev]
      exact mul_mem (hK _ inferInstance (fun x => Formalism.BasicNotions.Examples₂.LB.phi_mem i _) _) (Formalism.BasicNotions.Examples₂.LB.phi_mem i e)
    refine hKle ?_
    induction y using TensorProduct.inductionOn with
    | tmul a e => exact hmem a e
    | add y z hy hz => rw [map_add]; exact add_mem hy hz

end GlobalTheory.EvExtend
end
end

section

open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp

set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie
open Formalism.L2.Theta GlobalTheory.ExportSeries GlobalTheory.ConjTwist
open Formalism.L2.Host (embLL0)
open scoped TensorProduct


attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.BigOn.Exp

theorem coefLat_le_span {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
    {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F} {F : Face D A}
    {κw : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)} {v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec}
    {O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)} (hC : GlobalTheory.Hk3.Core R F) (hFW : Nonempty (FWTie T R κw v₀))
    (hio : IoExt R) (i : Fin D.R.m) (hO : OMPins T R κw v₀ O i) (B : Base (Vc D i) (Wc D i)) (hB : B.Good)
    (hBo : BaseOf R i B) {Oc Oc' : Subring ℂ} (hc : IsCoefRing (embLL0 D) (labLL0 D) Oc)
    (hc' : IsCoefRing (embLL0 D) (labLL0 D) Oc') (h : Bridge.Gf (Vc D i)) {P : PolF D (Wc D i).rank (Vc D i).rank}
    (hP : P ∈ B.coefLat (embLL0 D) (labLL0 D) Oc h) :
    P ∈ Submodule.span Oc (B.coefLat (embLL0 D) (labLL0 D) Oc' h : Set (PolF D (Wc D i).rank (Vc D i).rank)) := by
  obtain ⟨c, hcE, -, -⟩ := GlobalTheory.CoefExtC.exists_extC_bijective_unique D G Pl0 T0 A T R F κw v₀ hC hFW i Unit _ (O i) hO.2
  obtain ⟨u, w₀, hu, -, -⟩ := FWT.IsChosenExtremalVector.io _ hO.2.lift.v0 hio
  obtain ⟨κ, -, -, -, hL⟩ := GlobalTheory.CoefLatConj.coefLat_conj D G Pl0 T0 A T R F κw v₀ O hC hFW hio i hO c hcE u hu B hB hBo
  have e1 := (hL ↥D.LL0 (embLL0 D) (labLL0 D) Oc hc).1 h
  have e2 := (hL ↥D.LL0 (embLL0 D) (labLL0 D) Oc' hc').1 h
  rw [e1] at hP
  refine Submodule.span_mono ?_ hP
  intro Q hQ
  rw [SetLike.mem_coe, e2]
  exact Submodule.subset_span hQ

theorem baseOf_of_realPin_at {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T0 : Type}
    {A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
    {Rl : RealDat3 D A3 Ks} {cG : G0 Rl.Pg D.R.r ≃* G0g D.nd}
    (hL : Rl.toLevCh.Is A3.A.μ0) {ρ : Setup D.ntw} (hρ : ρ.Good) (hp : RealPin Rl cG ρ) (i : D.ntw.Tw)
    (j : Fin D.R.m) (b : Bool) : BaseOf Rl.toRealDat j (ρ.B i j b) := by
  have hB := hρ.base i j b
  have hlam := GlobalTheory.BaseLiftWeight.lam_eq D _ Rl.toLevCh A3.A.μ0 j (ρ.B i j b) hL hB (hp.mu0 i j b) (hp.ap i j b) (hp.am i j b)
  have hc : ∀ τ, (ρ.B i j b).w.c τ = liftC D j τ := fun τ => GlobalTheory.BaseLiftWeight.c_eq hL hB (hp.mu0 i j b) τ
  have hP : (ρ.B i j b).w.p = GlobalTheory.IndefiniteRowSideFullHecke.InfinityTypes.pS D j := funext fun τ => congrArg Prod.fst (hB.sig τ)
  have hQ : (ρ.B i j b).w.q = GlobalTheory.IndefiniteRowSideFullHecke.InfinityTypes.qS D j := funext fun τ => congrArg Prod.snd (hB.sig τ)
  have hAP : (ρ.B i j b).w.ap = GlobalTheory.IndefiniteRowSideFullHecke.InfinityTypes.aP D j := funext fun τ => hp.ap i j b τ
  have hAM : (ρ.B i j b).w.am = GlobalTheory.IndefiniteRowSideFullHecke.InfinityTypes.aM D j := funext fun τ => hp.am i j b τ
  refine
    { ψ := hp.psi i j b, θ := hp.inf i j b, sT := hp.cartT i j b, BS := hp.onbS i j b, BT := hp.onbT i j b,
      ΛS := hp.latS i j b, ΛT := hp.latT i j b, βS := hp.frS i j b, βT := hp.frT i j b, vac := hp.vac i j b,
      Pg := hp.Pg i j b, mu0 := hp.mu0 i j b, eta := hp.eta i j b, lam := hlam, delta := ?_, p := hP, q := hQ,
      c := funext hc }
  rw [← liftWeight_delta, Weight.delta, Weight.delta, hP, hQ, hAP, hAM]
  rfl

theorem smallInt_isCoefRing (D : D7) : IsCoefRing (embLL0 D) (labLL0 D) (smallInt D) :=
  ⟨embLL0_labLL0, fun a => ⟨a, rfl⟩⟩

end GlobalTheory.BigOn.Exp
end
end

section

open NumberField IsDedekindDomain Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.CovTop Formalism.L2.Pj GlobalTheory.FormTies GlobalTheory.Shares GlobalTheory.ShareOn GlobalTheory.ShareOn.Reading
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.ShareOn.Reading
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem castFrame_castFrame_symm {E : Type} [Field E] {r : ℕ} {Ψ Ψ' : Finset (E →+* ℂ)} (hΨ : Ψ = Ψ')
    (x : Frame Ψ' r) : castFrame hΨ (castFrame hΨ.symm x) = x := by
  subst hΨ; rfl


set_option synthInstance.maxHeartbeats 400000 in
theorem rdLin_linearIndependent {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L}
    {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX}
    {Csz : ℝ} {p : PtAt ex Csz} {r : TwoRuns p.T p.P.Gp} (h : RunsOk (fw2 p) r) {i : Fin D.R.m} {C : Type}
    [MulAction p.P.Gp C] {M : TwoLevels D.host.E D.R.r p.P.Gp C} {v : HeightOneSpectrum (𝓞 D.what₂.LL)}
    {e : C ≃ ((r.used v).full.U ((i : ℕ) + 1) (r.used v).full.σ₀).Comp}
    (ha : ∀ c, (M.comp c).toData = ((r.used v).full.U ((i : ℕ) + 1) (r.used v).full.σ₀).X (e c)) (n : ℕ)
    (b : Fin n → (recB (h.laws v).p.toLawsCore).Cusp ((i : ℕ) + 1) (p.κ i)) :
    LinearIndependent (recB (h.laws v).p.toLawsCore).KO b → LinearIndependent ℂ (fun k => rdLin h ha (b k)) := by
  intro hb
  have hJ := (GlobalTheory.ReadingTieCheck.tieRead_holds (h.laws v).p ((i : ℕ) + 1) ⟨Nat.le_add_left _ _, i.2⟩).2 (p.κ i)
  let b' : Fin n → cusp ((r.used v).full.Q.Xo ((i : ℕ) + 1)) (r.used v).full.Q.c ((r.used v).full.U ((i : ℕ) + 1))
      (wtA (p.κ i)) (p.κ i).n :=
    fun k => ⟨(b k).1, cutR_le (r.used v).full.C ((i : ℕ) + 1) (p.κ i) (b k).2⟩
  have hb' : LinearIndependent (r.used v).full.Q.c.F b' := by
    rw [Fintype.linearIndependent_iff] at hb ⊢
    intro g hg
    apply hb g
    apply Subtype.ext
    have h1 := congrArg Subtype.val hg
    simp only [Submodule.coe_sum, Submodule.coe_smul, Submodule.coe_zero] at h1 ⊢
    exact h1
  have hR := hJ n b' hb'
  rw [Fintype.linearIndependent_iff] at hR ⊢
  intro g hg
  apply hR g
  have hoff : ∀ k, rdC ((r.used v).full.U ((i : ℕ) + 1)) (r.used v).full.σ₀ (wtA (p.κ i)) (p.κ i).n (b' k) ∈
      offZero ((r.used v).full.U ((i : ℕ) + 1) (r.used v).full.σ₀).X :=
    fun k => rdU_mem_offZero _ _
  have claim : ∀ c, (∑ k, g k • rdC ((r.used v).full.U ((i : ℕ) + 1)) (r.used v).full.σ₀ (wtA (p.κ i)) (p.κ i).n
      (b' k)) (e c) = 0 := by
    intro c
    funext x
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    by_cases hx : x ∈ (((r.used v).full.U ((i : ℕ) + 1) (r.used v).full.σ₀).X (e c)).dom
    · have hy : castFrame (psi_eq ha c).symm x ∈ M.dom :=
        (mem_dom_iff ha c _).1 (by rw [castFrame_castFrame_symm]; exact hx)
      have := congrFun (congrFun hg c) ⟨_, hy⟩
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, rdLin_apply, rdFun,
        castFrame_castFrame_symm] at this
      exact this
    · exact Finset.sum_eq_zero fun k _ => by rw [hoff k (e c) x hx, mul_zero]
  funext k'
  have := claim (e.symm k')
  rw [e.apply_symm_apply] at this
  exact this

end GlobalTheory.ShareOn.Reading
end
end

section

open NumberField IsDedekindDomain Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.CovTop Formalism.L2.Pj GlobalTheory.FormTies GlobalTheory.Shares GlobalTheory.ShareOn GlobalTheory.ShareOn.Reading

set_option autoImplicit false

namespace GlobalTheory.ShareOn.Reading

section Onto
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem ss_transport {X X' : Data E r} (hX : X = X') {Ψ : Finset (E →+* ℂ)} (h1 : X.Ψ = Ψ) (h2 : X'.Ψ = Ψ)
    (g : Frame Ψ r → ℂ) (la : Wt Ψ r) (la' : Wt X'.Ψ r)
    (hla : ∀ τ (t1 : τ ∈ Ψ) (t2 : τ ∈ X'.Ψ) a, la ⟨τ, t1⟩ a = la' ⟨τ, t2⟩ a)
    (hg : (fun x => g (castFrame h1 x)) ∈ X.SS (castWt h1 la)) :
    (fun y => g (castFrame h2 y)) ∈ X'.SS la' := by
  subst hX
  have hw : castWt h1 la = la' := by
    funext τ a
    exact hla τ.1 _ τ.2 a
  rw [← hw]
  exact hg

end Onto

theorem rdFun_onto {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D}
    {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} {p : PtAt ex Csz}
    {r : TwoRuns p.T p.P.Gp} (h : RunsOk (fw2 p) r) {i : Fin D.R.m} {C : Type} [MulAction p.P.Gp C]
    {M : TwoLevels D.host.E D.R.r p.P.Gp C} {ka : Wt M.Ψ D.R.r} {v : HeightOneSpectrum (𝓞 D.what₂.LL)}
    {e : C ≃ ((r.used v).full.U ((i : ℕ) + 1) (r.used v).full.σ₀).Comp}
    (ha : ∀ c, (M.comp c).toData = ((r.used v).full.U ((i : ℕ) + 1) (r.used v).full.σ₀).X (e c))
    (hb : ∀ c τ (h1 : τ ∈ M.Ψ) (h2 : τ ∈ (((r.used v).full.U ((i : ℕ) + 1) (r.used v).full.σ₀).X (e c)).Ψ) a,
      ka ⟨τ, h1⟩ a = laR (r.used v).full.toTop ((i : ℕ) + 1) (p.κ i) (e c) ⟨τ, h2⟩ a) :
    0 < badN D → 8 * D.R.f * D.R.r + 4 ≤ D.R.nV → ∀ (G : C → Frame M.Ψ D.R.r → ℂ), G ∈ M.SS ka →
      ∃ (m : ℕ) (α : Fin m → ℂ) (Fs : Fin m → (recB (h.laws v).p.toLawsCore).Cusp ((i : ℕ) + 1) (p.κ i)),
        ∀ c, ∀ x ∈ M.dom, G c x = ∑ k, α k * rdFun h ha (Fs k) c x := by
  intro hN hnV G hG
  classical
  have ha' : ∀ k, (M.comp (e.symm k)).toData = ((r.used v).full.U ((i : ℕ) + 1) (r.used v).full.σ₀).X k := fun k => by
    rw [ha (e.symm k), e.apply_symm_apply]
  have hΨk : ∀ k, M.Ψ = (((r.used v).full.U ((i : ℕ) + 1) (r.used v).full.σ₀).X k).Ψ := fun k => by
    rw [← ha' k]; exact (M.comp_Ψ _).symm
  have hb' : ∀ k τ (h1 : τ ∈ M.Ψ) (h2 : τ ∈ (((r.used v).full.U ((i : ℕ) + 1) (r.used v).full.σ₀).X k).Ψ) a,
      ka ⟨τ, h1⟩ a = laR (r.used v).full.toTop ((i : ℕ) + 1) (p.κ i) k ⟨τ, h2⟩ a := by
    intro k
    obtain ⟨c, rfl⟩ := e.surjective k
    exact hb c

  have hf : 0 < D.R.f := lt_of_lt_of_le (lt_of_le_of_lt (Nat.zero_le _) i.2) D.R.m_le_f
  have hTau : Nonempty D.what₂.Tau := by
    rw [← Fintype.card_pos_iff, D.what₂.card_Tau]; exact hf
  obtain ⟨τ0⟩ := hTau
  have hn : 8 * D.R.f * D.R.r + 4 ≤ (p.κ i).n := by
    rw [(p.fw.kap i τ0).2.2]; exact hnV
  have hOnto : RdOnto (h.laws v).p ((i : ℕ) + 1) (p.κ i) :=
    GlobalTheory.Shares.rdOnto_rec GlobalTheory.chartIndependence_unconditional D (r.used v).full.toTop (h.laws v).p ((i : ℕ) + 1)
      (GlobalTheory.OnTies.inR_succ i) (h.laws v).sh
      (GlobalTheory.RunIn.gamAt_of_lawsCore D _ (h.laws v).p.toLawsCore) hN
      (GlobalTheory.Dict.gram_xi_eq_of_lawsFull (h.laws v)) (p.κ i) hn
      (ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.lastPos_wtA (h.laws v).p (GlobalTheory.OnTies.inR_succ i) _ (lastPos_kappa p i))
  let f : ∀ k : ((r.used v).full.U ((i : ℕ) + 1) (r.used v).full.σ₀).Comp, Frame (((r.used v).full.U ((i : ℕ) + 1) (r.used v).full.σ₀).X k).Ψ D.R.r → ℂ := fun k y => G (e.symm k) (castFrame (hΨk k).symm y)
  have hfm : ∀ k, f k ∈ (((r.used v).full.U ((i : ℕ) + 1) (r.used v).full.σ₀).X k).SS (laR (r.used v).full.toTop ((i : ℕ) + 1) (p.κ i) k) := fun k =>
    ss_transport (ha' k) (M.comp_Ψ (e.symm k)) (hΨk k).symm (G (e.symm k)) ka _ (hb' k) (hG (e.symm k))
  obtain ⟨m, α, Fs, -, hsum⟩ := hOnto f hfm
  refine ⟨m, α, Fs, fun c x hx => ?_⟩
  have hy := (mem_dom_iff ha c x).2 hx
  have key := hsum (e c) _ hy
  have hl : f (e c) (castFrame (psi_eq ha c) x) = G c x := by
    show G (e.symm (e c)) (castFrame (hΨk (e c)).symm (castFrame (psi_eq ha c) x)) = G c x
    have hc : e.symm (e c) = c := e.symm_apply_apply c
    have hx' : castFrame (hΨk (e c)).symm (castFrame (psi_eq ha c) x) = x := rfl
    rw [hx', hc]
  rw [← hl, key]
  rfl

end GlobalTheory.ShareOn.Reading
end

section

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.CovTop Formalism.L2.Pj GlobalTheory.FormTies GlobalTheory.Shares
open ReciprocityTheory.ChartRestriction.G.PullbackSections.PfModelLatA GlobalTheory.ShareOn

namespace GlobalTheory.ShareOn

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ}

def MovesAt (p : PtAt ex Csz) (r : TwoRuns p.T p.P.Gp) (i : Fin D.R.m) (v : HeightOneSpectrum (𝓞 D.what₂.LL))
    (γ : LaMod (p.T.Q.Dw ((i : ℕ) + 1)) p.T.Q.l ≃ₗ[𝓞 D.host.E] LaMod (p.T.Q.Dw ((i : ℕ) + 1)) p.T.Q.l)
    (k k' : (uAt r v i).Comp) (a : GL (Fin D.R.r) D.host.E)
    (hm : GlobalTheory.LevelCusp.IsMatch ((uAt r v i).X k) ((uAt r v i).X k') a)
    (x : Frame ((uAt r v i).X k).Ψ D.R.r) (hx : x ∈ ((uAt r v i).X k).dom) : Prop :=
  ∃ (hy : castFrame hm.psi (lact a x) ∈ ((uAt r v i).X k').dom) (t : _),
    FrBor t ((uAt r v i).un k' ⟨castFrame hm.psi (lact a x), hy⟩) (mvLev ((r.used v).full.Q.Xo ((i : ℕ) + 1)) (r.used v).full.Q.c γ ((uAt r v i).un k ⟨x, hx⟩))

def ReadsInv (p : PtAt ex Csz) (r : TwoRuns p.T p.P.Gp) (i : Fin D.R.m) (v : HeightOneSpectrum (𝓞 D.what₂.LL))
    (ψ : ∀ k : (uAt r v i).Comp, LaMod (p.T.Q.Dw ((i : ℕ) + 1)) p.T.Q.l ≃ₗ[𝓞 D.host.E] latQ p r i v k)
    (γ : LaMod (p.T.Q.Dw ((i : ℕ) + 1)) p.T.Q.l ≃ₗ[𝓞 D.host.E] LaMod (p.T.Q.Dw ((i : ℕ) + 1)) p.T.Q.l)
    (k k' : (uAt r v i).Comp) (a : GL (Fin D.R.r) D.host.E) : Prop :=
  ∀ w : lattice₂ D ((uAt r v i).X k).Λ,
    ∃ hw : Matrix.mulVec (a : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E) (w : Fin D.R.r → D.host.E) ∈
        lattice₂ D ((uAt r v i).X k').Λ,
      Submodule.Quotient.mk (p := p.T.Q.l.Mb • (⊤ : Submodule (𝓞 D.host.E) (lattice₂ D ((uAt r v i).X k').Λ))) ⟨_, hw⟩ =
        ψ k' (γ.symm ((ψ k).symm (Submodule.Quotient.mk w)))

theorem isTransp_of_movesAt {p : PtAt ex Csz} {r : TwoRuns p.T p.P.Gp} {i : Fin D.R.m}
    {v : HeightOneSpectrum (𝓞 D.what₂.LL)}
    {ψ : ∀ k : (uAt r v i).Comp, LaMod (p.T.Q.Dw ((i : ℕ) + 1)) p.T.Q.l ≃ₗ[𝓞 D.host.E] latQ p r i v k}
    {γ : LaMod (p.T.Q.Dw ((i : ℕ) + 1)) p.T.Q.l ≃ₗ[𝓞 D.host.E] LaMod (p.T.Q.Dw ((i : ℕ) + 1)) p.T.Q.l}
    {k k' : (uAt r v i).Comp} {a : GL (Fin D.R.r) D.host.E}
    (hm : GlobalTheory.LevelCusp.IsMatch ((uAt r v i).X k) ((uAt r v i).X k') a)
    (h₁ : ∀ x hx, MovesAt p r i v γ k k' a hm x hx) (h₂ : ReadsInv p r i v ψ γ k k' a) :
    IsTransp p r i v ψ γ k k' a :=
  ⟨hm, h₁, h₂⟩

end GlobalTheory.ShareOn

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical


theorem _root_.GlobalTheory.T.weilOperator_archimedeanSlice_schwartzSeminorm_bounded : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
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
  ∀ Φ ∈ GlobalTheory.WeilM.schA D.host.F κ, ∀ (y : κ → FiniteAdeleRing (𝓞 D.host.F) D.host.F) p0 (k n : ℕ), ∃ C : ℝ,
      ∀ᶠ p in nhds p0, ∀ x : κ → mixedEmbedding.mixedSpace D.host.F,
        ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (fun x => om p Φ (GlobalTheory.WeilCont.adeleJoin D.host.F x y)) x‖ ≤ C := by
  first | exact @GlobalTheory.WeilCont.slice_bounds | exact GlobalTheory.WeilCont.slice_bounds | (intros; apply GlobalTheory.WeilCont.slice_bounds <;> assumption)
end
