module

public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle205
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle232
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle193
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle196
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
public import Development.AbelianVarietyTheory.Statements.EllipticCurveLevels.Bundle001
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle296
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle315
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle338
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle297
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NontrivialOfNeBot
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceUnitaryLocalPointsEquivGL
public import Formalism.LocalToGlobal.Columns.Bundle023
public import Formalism.LocalToGlobal.Columns.ChainInstY
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PredMemGamRanks
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle237
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemZmuOfPowPred
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SmulCompSmul
import Formalism.LocalToGlobal.Columns.ChainInst
public import Formalism.LocalToGlobal.Columns.Bundle033
public import Formalism.LocalToGlobal.Columns.Bundle026
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.Bundle001
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.MemGoodPrimesOfNoExceptional
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.PenultimateKernelDiamondInvariant
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.ThDistC
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.TopLawQ
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Hk3.CorrInert

variable {D : D7}

theorem exists_idem_of_conj_eq (P : Pl D.host.E) (hP : _root_.Formalism.DivisionValues.conjPl P = P) : ∃ e, IsPrimeIdem P e e := by
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.IdemSupport.exists_comp D
  obtain ⟨e, f, h⟩ := GlobalTheory.IdemSupport.exists_isPrimeIdem hΦ P
  have hc : P = GlobalTheory.IdemSupport.cP P := by
    refine (GlobalTheory.IdemSupport.isConjPl_iff P P).1 fun c hc => ⟨GlobalTheory.IdemSupport.cO D c, ?_, rfl⟩
    have h1 : GlobalTheory.IdemSupport.cO D c ∈ (_root_.Formalism.DivisionValues.conjPl P).asIdeal := Ideal.mem_map_of_mem _ hc
    rwa [hP] at h1
  rcases h with ⟨h, -⟩ | h
  · exfalso
    have hd := GlobalTheory.IdemSupport.delta_of_isIdemAt hΦ h
    have hd' := GlobalTheory.IdemSupport.delta_conj hΦ hd
    rw [← hc] at hd'
    have h2 := GlobalTheory.IdemSupport.ev_mul (Φ := Φ) e (cA D e) P
    rw [h.1.2.1, GlobalTheory.IdemSupport.ev_zero, hd.2.1, hd'.2.1, one_mul] at h2
    exact zero_ne_one h2
  · obtain ⟨rfl, h⟩ := h
    exact ⟨f, Or.inr ⟨rfl, h⟩⟩

theorem suppF_of_mem_rep (V : HSp D) {P : Pl D.host.E} {e f : AE D} (he : IsPrimeIdem P e f) {d : List ℤ}
    {γ : GA D V} (h : γ ∈ rep V P d) : SuppF V f γ := by
  unfold rep at h
  split_ifs at h with hl
  · obtain ⟨e', f', -, -, -, he', -, -, -, -, -, -, -, hs, -⟩ := hl.choose_spec
    obtain ⟨-, rfl⟩ :=
      ((GlobalTheory.IdemSupport.supported_group_and_prime_idempotents V).2.2.1 P e f he).2.2.2.1 e' f' he'
    exact hs γ h
  · exact absurd h (Finset.notMem_empty _)

theorem exists_pullback {V : HSp D} {P : Pl D.host.E} {e f : AE D} (he : IsPrimeIdem P e f)
    {W : Type} [AddCommGroup W] [Module ℂ W] (π : GA D V →* Module.End ℂ W) {H : Type} (ι : H → GA D V)
    (hι : ∀ g, SuppF V f g → ∃ h, ι h = g) (c : List ℤ →₀ ℂ) :
    ∃ b : H →₀ ℂ, ∀ u, (b.sum fun h z => z • π (ι h) u) = opOf π P c u := by
  have hm : opOf π P c ∈ Submodule.span ℂ (Set.range fun h => π (ι h)) := by
    refine Submodule.sum_mem _ fun d _ => Submodule.smul_mem _ _ (Submodule.sum_mem _ fun γ hγ => ?_)
    obtain ⟨h, rfl⟩ := hι γ (suppF_of_mem_rep V he hγ)
    exact Submodule.subset_span ⟨h, rfl⟩
  obtain ⟨b, hb⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 hm
  refine ⟨b, fun u => ?_⟩
  rw [← hb]
  simp only [Finsupp.sum, LinearMap.sum_apply, LinearMap.smul_apply]

theorem half {S T : HSp D} {P : Pl D.host.E} {e f : AE D} (he : IsPrimeIdem P e f)
    {W : Type} [AddCommGroup W] [Module ℂ W] (πS : GA D S →* Module.End ℂ W) (πT : GA D T →* Module.End ℂ W)
    (comm : ∀ g h u, πS g (πT h u) = πT h (πS g u)) (Vac : W → Prop)
    (fixS : ∀ u, Vac u → ∀ k ∈ hyp S P, πS k u = u) (fixT : ∀ u, Vac u → ∀ k ∈ hyp T P, πT k u = u)
    {GS GT : Type} (ιS : GS → GA D S) (ιT : GT → GA D T) (hS : ∀ g, SuppF S f (ιS g))
    (hT : ∀ g, SuppF T f g → ∃ h, ιT h = g)
    (howe : ∀ bT : GT →₀ ℂ, (∀ u, Vac u → ∀ k ∈ hyp T P,
        πT k (bT.sum fun h z => z • πT (ιT h) u) = bT.sum fun h z => z • πT (ιT h) u) →
      ∃ bS : GS →₀ ℂ, ∀ u, Vac u → (bT.sum fun h z => z • πT (ιT h) u) = bS.sum fun g z => z • πS (ιS g) u)
    (cT : List ℤ →₀ ℂ) : ∃ cS, ∀ u, Vac u → opOf πS P cS u = opOf πT P cT u := by
  classical
  obtain ⟨bT, hb⟩ := exists_pullback he πT ιT hT cT
  obtain ⟨bS, hbS⟩ := howe bT fun u hu k hk => by
    rw [hb]
    exact (GlobalTheory.T.spherical_label_operators_on_hyperspecial_fixed_vectors T P).2.1 cT W πT u (fixT u hu) k hk
  obtain ⟨cS, hc⟩ := GlobalTheory.T.exists_sphericalCombination_of_fixed_localTranslates S P e f he (Finsupp.mapDomain ιS bS) fun g hg => by
    obtain ⟨g', -, rfl⟩ := Finset.mem_image.1 (Finsupp.mapDomain_support hg)
    exact hS g'
  refine ⟨cS, fun u hu => ?_⟩
  have e1 : ((Finsupp.mapDomain ιS bS).sum fun g z => z • πS g u) = bT.sum fun h z => z • πT (ιT h) u := by
    rw [hbS u hu]
    exact Finsupp.sum_mapDomain_index (h := fun g (z : ℂ) => z • πS g u) (fun _ => zero_smul _ _)
      (fun _ _ _ => add_smul _ _ _)
  rw [← hc W πS u (fixS u hu) fun k hk => ?_, e1, hb]

  rw [e1, Finsupp.sum, map_sum]
  refine Finset.sum_congr rfl fun h _ => ?_
  rw [map_smul, comm, fixS u hu k hk]

theorem coe_sum_smul {W : Type} [AddCommGroup W] [Module ℂ W] {M : Submodule ℂ W} {H : Type} (b : H →₀ ℂ) (v : H → M) :
    ((b.sum fun h z => z • v h : M) : W) = b.sum fun h z => z • (v h : W) := by
  simp only [Finsupp.sum, Submodule.coe_sum, Submodule.coe_smul]

theorem sphCorr_of_inert : HoweUnram → ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (P : Pl D.host.E), IsWeilDatumO ψ S T χS χT om → _root_.Formalism.DivisionValues.conjPl P = P → VacFix ψ om P → SphCorr ψ om P := by
  intro hH D ψ S T χS χT om P hW hP hV
  obtain ⟨e, he⟩ := exists_idem_of_conj_eq P hP
  obtain ⟨ϖ, σ, q, δ, JS, JT, ψ', M, ρ, ω, ιS, ιT, hL, rS, rT, kS, kT, hω, hM, hvac⟩ :=
    GlobalTheory.T.exists_unramifiedLocalPair_of_inertWeilDatum ψ S T χS χT om P hW hP hV e he
  haveI : CharZero (P.adicCompletion D.host.E) := algebraRat.charZero _
  obtain ⟨h1, h2⟩ := GlobalTheory.T.howeUnramified_all_vacua hH _ ϖ σ q δ _ _ JS JT ψ' M ρ ω hL
  have oneS : (1 : GA D S) ∈ hyp S P := by
    rw [← map_one ιS, kS]; exact one_mem _
  have oneT : (1 : GA D T) ∈ hyp T P := by
    rw [← map_one ιT, kT]; exact one_mem _
  have comm : ∀ g h u, (om.comp (MonoidHom.inl _ _)) g ((om.comp (MonoidHom.inr _ _)) h u) =
      (om.comp (MonoidHom.inr _ _)) h ((om.comp (MonoidHom.inl _ _)) g u) := by
    intro g h u
    change (om (g, 1) * om (1, h)) u = (om (1, h) * om (g, 1)) u
    rw [← map_mul, ← map_mul, Prod.mk_mul_mk, Prod.mk_mul_mk, one_mul, mul_one, one_mul, mul_one]
  have fixS : ∀ u, IsVacAt ψ S T P u → ∀ k ∈ hyp S P, (om.comp (MonoidHom.inl _ _)) k u = u :=
    fun u hu k hk => hV u hu k hk 1 oneT
  have fixT : ∀ u, IsVacAt ψ S T P u → ∀ k ∈ hyp T P, (om.comp (MonoidHom.inr _ _)) k u = u :=
    fun u hu k hk => hV u hu 1 oneS k hk
  have ωS : ∀ g (m : M), ((ω (g, 1) m : M) : WO S T → ℂ) = (om.comp (MonoidHom.inl _ _)) (ιS g) m := by
    intro g m
    rw [hω, map_one]; rfl
  have ωT : ∀ h (m : M), ((ω (1, h) m : M) : WO S T → ℂ) = (om.comp (MonoidHom.inr _ _)) (ιT h) m := by
    intro g m
    rw [hω, map_one]; rfl
  refine ⟨hV, fun cT => ?_, fun cS => ?_⟩
  · refine half he _ _ comm (IsVacAt ψ S T P) fixS fixT ιS ιT (fun g => (rS _).1 ⟨g, rfl⟩)
      (fun g hg => (rT g).2 hg) (fun bT hb => ?_) cT
    obtain ⟨bS, hbS⟩ := h1 bT fun s hs k hk => by
      apply Subtype.ext
      rw [ωT, coe_sum_smul]
      simp only [ωT]
      exact hb s ((hvac s).1 hs) _ ((kT k).2 hk)
    refine ⟨bS, fun u hu => ?_⟩
    have := congrArg Subtype.val (hbS ⟨u, hM u hu⟩ ((hvac _).2 hu))
    rw [coe_sum_smul, coe_sum_smul] at this
    simpa only [ωS, ωT] using this
  · suffices h : ∃ cT, ∀ u, IsVacAt ψ S T P u →
        opOf (om.comp (MonoidHom.inr _ _)) P cT u = opOf (om.comp (MonoidHom.inl _ _)) P cS u from
      h.imp fun cT h u hu => (h u hu).symm
    refine half he _ _ (fun g h u => (comm h g u).symm) (IsVacAt ψ S T P) fixT fixS ιT ιS (fun g => (rT _).1 ⟨g, rfl⟩)
      (fun g hg => (rS g).2 hg) (fun bS hb => ?_) cS
    obtain ⟨bT, hbT⟩ := h2 bS fun s hs k hk => by
      apply Subtype.ext
      rw [ωS, coe_sum_smul]
      simp only [ωS]
      exact hb s ((hvac s).1 hs) _ ((kS k).2 hk)
    refine ⟨bT, fun u hu => ?_⟩
    have := congrArg Subtype.val (hbT ⟨u, hM u hu⟩ ((hvac _).2 hu))
    rw [coe_sum_smul, coe_sum_smul] at this
    simpa only [ωS, ωT] using this

end GlobalTheory.Hk3.CorrInert

end
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU GlobalTheory.CuspRep GlobalTheory.PRep

noncomputable section

namespace GlobalTheory.Cong

theorem exists_continuous_inv_cLoc {E : Type} [Field E] [NumberField E] [IsCMField E] (n : ℕ)
    (w₀ : HeightOneSpectrum (𝓞 E)) :
    ∃ ι : GL (Fin n) (w₀.adicCompletion E) → GA E n, Continuous ι ∧ ι 1 = 1 ∧
      ∀ x : UA E n, x ∈ locU n w₀ → ι (cLoc w₀ x) = x.1 := by
  by_cases hsp : IsSplitAt w₀
  · obtain ⟨e, he⟩ := GlobalTheory.locU_equiv_GL E n w₀ hsp
    refine ⟨fun h => ((e.symm h : locU n w₀) : UA E n).1,
      continuous_subtype_val.comp (continuous_subtype_val.comp e.symm.continuous), by simp, fun x hx => ?_⟩
    have h1 : e.symm (cLoc w₀ x) = ⟨x, hx⟩ := by
      rw [← he ⟨x, hx⟩]
      exact e.symm_apply_apply _
    simp only [h1]
  · have hc0 : GlobalTheory.CuspRep.conjSrc (IsCMField.complexConj E).toRingEquiv w₀ = w₀ := by
      by_contra hne
      exact hsp ⟨_, hne, GlobalTheory.DefU.LocRet.under_conjSrc w₀⟩
    have hw : GlobalTheory.Mem.Chr.ConjPl (IsCMField.complexConj E).toRingEquiv w₀ w₀ := by
      have h := GlobalTheory.SplitPts.conjPl_self_conjSrc (E := E) w₀
      change GlobalTheory.Mem.Chr.ConjPl _ w₀ (GlobalTheory.CuspRep.conjSrc (IsCMField.complexConj E).toRingEquiv w₀) at h
      rwa [hc0] at h
    refine ⟨fun h => finGL E n (locGL E n w₀ h),
      GlobalTheory.DefU.Inert.continuous_finGL.comp (GlobalTheory.CuspRep.CuspSub.continuous_locGL w₀), by simp,
      fun x hx => GlobalTheory.DefU.Inert.finGL_cLoc hw ⟨x, hx⟩⟩

theorem exists_algForm_ofType : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (lam : (E →+* ℂ) → DomWeight n) (K : Subgroup (UA E n)) (U : Submodule ℂ (UA E n → ℂ)), K ≤ finU (E := E) (n := n) → OfType lam K U → ∀ w₀ : HeightOneSpectrum (𝓞 E), ∃ (W : Wt E n) (f : algForms W), (∀ τ, W.at τ = lam τ) ∧ f ≠ 0 ∧ (∀ v, f.1 v ∈ U) ∧ (∀ k ∈ K, ∀ v g, f.1 v (g * k) = f.1 v g) ∧ ∃ N ∈ nhds (1 : GL (Fin n) (w₀.adicCompletion E)), ∀ x ∈ locU n w₀, cLoc w₀ x ∈ N → ∀ v g, f.1 v (g * x) = f.1 v g := by
  intro E _ _ _ n lam K U hK hU w₀
  classical
  let π : AutSub E n := ⟨U, hU.aut⟩
  set W := (AU.mk π).wt with hWdef
  have hWat : ∀ τ, W.at τ = lam τ := fun τ => by
    have h1 : (AU.mk π).HasWt τ (lam τ) := (AU.hasWt_mk π τ (lam τ)).2 (hU.wt τ)
    exact hasWeightAt_unique π τ ((AU.hasWt_mk π τ _).1 h1.wt) (hU.wt τ)
  let M := π.finPart W
  have hM0 : M ≠ ⊥ := AutSub.finPart_wt_ne_bot E n π
  have hV : π.V = Pairs.img (Pairs.jOf W M) := Pairs.V_eq_img π (Pairs.finPart_stable π W) hM0 le_rfl
  obtain ⟨φ, hφU, hφ0, hφK⟩ := hU.fix
  haveI : Nontrivial W.Sp := (Pairs.nontrivial_of_ne_bot hM0).1
  let b := Module.finBasis ℂ W.Sp
  obtain ⟨c, hc⟩ : φ ∈ LinearMap.range (Pairs.total b (Pairs.jOf W M)) := by
    rw [Pairs.range_total, ← hV]
    exact hφU
  let Fx : Submodule ℂ (UA E n → ℂ) :=
    { carrier := {ψ | ∀ k ∈ K, RU E n k ψ = ψ}
      add_mem' := fun {x y} hx hy k hk => by
        simp only [Set.mem_setOf_eq] at hx hy ⊢
        rw [map_add (f := _), hx k hk, hy k hk]
      zero_mem' := fun k _ => map_zero _
      smul_mem' := fun r ψ h k hk => by
        simp only [Set.mem_setOf_eq] at h ⊢
        rw [map_smul, h k hk] }
  have hFx : ∀ x : infU E n, ∀ u ∈ Fx, RU E n x.1 u ∈ Fx := fun x u hu k hk => by
    change RU E n k (RU E n x.1 u) = RU E n x.1 u
    rw [RU_RU, fin_mul_inf (hK hk) x.2, ← RU_RU, hu k hk]
  have hcF : ∀ a v, Pairs.jOf W M (c a) v ∈ Fx := Pairs.coeff_mem (Pairs.span_rep W) (R := fun x => RU E n x.1)
    (Pairs.jOf_rep W M) hFx b (by rw [hc]; exact hφK)
  obtain ⟨a, ha⟩ : ∃ a, c a ≠ 0 := by
    by_contra h
    push_neg at h
    apply hφ0
    rw [← hc, Pairs.total_apply]
    simp [h]
  have hS : IsOpen {k : finU (E := E) (n := n) | algRep W k (c a).1 = (c a).1} := isSmooth_algRep W (c a).1
  obtain ⟨ι, hι, hι1, hιx⟩ := exists_continuous_inv_cLoc n w₀
  have hS1 : {k : finU (E := E) (n := n) | algRep W k (c a).1 = (c a).1} ∈ nhds (1 : finU (E := E) (n := n)) :=
    hS.mem_nhds (by
      show algRep W 1 (c a).1 = (c a).1
      rw [map_one]
      rfl)
  rw [nhds_subtype, Filter.mem_comap] at hS1
  obtain ⟨T1, hT1, hT1S⟩ := hS1
  rw [nhds_subtype, Filter.mem_comap] at hT1
  obtain ⟨T, hT, hTT1⟩ := hT1
  refine ⟨W, (c a).1, hWat, fun h => ha (Subtype.ext h), fun v => AutSub.mem_finPart.1 (c a).2 v,
    fun k hk v g => congrFun (hcF a v k hk) g, ι ⁻¹' T, hι.continuousAt.preimage_mem_nhds (by rw [hι1]; exact hT),
    fun x hx hxN v g => ?_⟩
  have hxfin : x ∈ finU (E := E) (n := n) := (Subgroup.mem_inf.1 hx).1
  have h2 : x.1 ∈ T := hιx x hx ▸ hxN
  have hk : (⟨x, hxfin⟩ : finU (E := E) (n := n)) ∈ {k : finU (E := E) (n := n) | algRep W k (c a).1 = (c a).1} := hT1S (hTT1 h2)
  exact congrFun (LinearMap.congr_fun (congrArg Subtype.val hk) v) g

end GlobalTheory.Cong

end
end

section

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker NumberField IsDedekindDomain Classical

noncomputable section

namespace GlobalTheory.StabTopLaw



theorem xiTop_stab_law : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (G : ChGlob X R.m) (m2 : ℕ), X.Ok → Pr.Ok → IsSel X sel → (∀ i, Pr.g i ∈ S) → (∀ v, Pr.T v ∈ S) → L.Ok Ch sel mu cst G m2 → Ch.Ok → cst.sharp = true → R.m ≤ cst.A → (∀ j, j ≤ m2 + 1 → ∀ (b : L.β j) (P : rowSG Pr sel mu), P.1 ∈ Pr.vGs → L.h j b P = 1) → 2 * cst.M ≤ twTopDepth R → ∀ (u : Pr.Word) (p : ChPt (R := R) sel mu u (m2 + 1)) (Y : Set (Sp X.E (R.N (m2 + 1)))) (p' : ChPt (R := R) sel mu u (m2 + 1 + 1)) (a : FrmG (twLt Ch (m2 + 1 + 1)) (twTt (R := R) sel mu (m2 + 1 + 1))), Y ∈ ybSet sel mu cst p.deco.1.N → a • p' = p' → ∀ x, XiTop Ch sel mu cst (m2 + 1) p Y p' (a.1.1.toLinearMap ∘ₗ x) * ∏ P : rowSG Pr sel mu, muAt Ch sel mu cst (m2 + 1) P ((LinearEquiv.det a.1.1 : X.Eˣ) : X.E) = (((twLt Ch (m2 + 1 + 1)).chr a.2.1 * (twTt (R := R) sel mu (m2 + 1 + 1)).chr a.2.2 : X.Kˣ) : X.K) * XiTop Ch sel mu cst (m2 + 1) p Y p' x := by
  intro X Pr R Ch sel S mu cst L G m2 hX hPr hsel hgS hTS hL hCh hsh hA hb hMd u p Y p' a hY hfix x
  have hm : R.m = m2 + 2 := hL.hm
  have hc : cst.Ok := hL.cst_ok
  have hn : TopNum R (m2 + 1) := topNum_of hm
  have hS : QSep Pr sel mu := qSep_of sel mu hPr hsel hgS
  have hU : QUnif sel mu := qUnif_of sel mu hX hPr hsel
  have hLaw := topLawG_sym Ch sel mu cst control_phi_law hX hPr hm hsh
  have hRow := lastRow_colLevSym Ch hm
  choose κ' hκ' hκr' hκQ' using fun w : rowSG Pr sel mu =>
    frsF_smulQ sel mu u p' (twLt Ch (m2 + 1 + 1)) (twTt (R := R) sel mu (m2 + 1 + 1)) a w
  rw [hfix] at hκ'
  have e0 : phiT X.K p.deco.1 p'.deco.1 (a.1.1.toLinearMap ∘ₗ x) = phiT X.K p.deco.1 p'.deco.1 x := by
    have h := phiT_smul X.K p.deco p'.deco 1 1 a.1 (a.2.1 : GLG (E := X.E) (n := R.N (m2 + 1 + 1)) (SG := Pr.vGs)) x
    have hd : (a • p').deco = (a.1, (a.2.1 : GLG (E := X.E) (n := R.N (m2 + 1 + 1)) (SG := Pr.vGs))) • p'.deco := rfl
    rw [← hd, hfix, ← Prod.one_eq_mk, one_smul] at h
    exact h

  rw [XiTop_eq, XiTop_eq, e0]

  have hsym : ∀ w z, (frsF sel mu p' w).symm (a.1.1 z) = (κ' w).1.symm ((frsF sel mu p' w).symm z) := by
    intro w z
    have h := hκ' w
    generalize frsF sel mu p' w = F' at h ⊢
    rw [LinearEquiv.symm_apply_eq]
    calc a.1.1 z = (a.1.1 * F' * (κ' w).1) ((κ' w).1.symm (F'.symm z)) := by
          simp only [LinearEquiv.mul_apply, LinearEquiv.apply_symm_apply]
      _ = F' ((κ' w).1.symm (F'.symm z)) := by rw [← h]
  have hF : ∀ w, inFr (frsF sel mu p w) (frsF sel mu p' w) (a.1.1.toLinearMap ∘ₗ x) =
      (κ' w).1.symm.toLinearMap ∘ₗ inFr (frsF sel mu p w) (frsF sel mu p' w) x := by
    intro w
    apply LinearMap.ext
    intro v
    simp only [inFr, LinearMap.comp_apply, LinearEquiv.coe_coe]
    exact hsym w _

  have hdet : ∀ w, ((LinearEquiv.det a.1.1 : X.Eˣ) : X.E) = ((LinearEquiv.det ((κ' w)⁻¹).1 : X.Eˣ) : X.E) := by
    intro w
    have hd := congrArg (fun f => ((LinearEquiv.det f : X.Eˣ) : X.E)) (hκ' w)
    simp only [map_mul, Units.val_mul] at hd
    have hdF : ((LinearEquiv.det (frsF sel mu p' w) : X.Eˣ) : X.E) ≠ 0 := Units.ne_zero _
    have hdK : ((LinearEquiv.det (κ' w).1 : X.Eˣ) : X.E) ≠ 0 := Units.ne_zero _
    have hAK : ((LinearEquiv.det a.1.1 : X.Eˣ) : X.E) * ((LinearEquiv.det (κ' w).1 : X.Eˣ) : X.E) = 1 := by
      have h2 : ((LinearEquiv.det (frsF sel mu p' w) : X.Eˣ) : X.E) *
          (((LinearEquiv.det a.1.1 : X.Eˣ) : X.E) * ((LinearEquiv.det (κ' w).1 : X.Eˣ) : X.E)) =
          ((LinearEquiv.det (frsF sel mu p' w) : X.Eˣ) : X.E) * 1 := by
        rw [mul_one]
        conv_rhs => rw [hd]
        ring
      exact mul_left_cancel₀ hdF h2
    have e1 : ((LinearEquiv.det ((κ' w)⁻¹).1 : X.Eˣ) : X.E) = ((LinearEquiv.det (κ' w).1 : X.Eˣ) : X.E)⁻¹ := by
      show ((LinearEquiv.det ((κ' w).1)⁻¹ : X.Eˣ) : X.E) = _
      rw [map_inv, Units.val_inv_eq_inv_val]
    rw [e1]
    exact eq_inv_of_mul_eq_one_left hAK

  have hmu : ∀ w, muAt Ch sel mu cst (m2 + 1) w ((LinearEquiv.det a.1.1 : X.Eˣ) : X.E) =
      rhoT Ch sel mu (m2 + 1) w ((LinearEquiv.det (κ' w).1 : X.Eˣ) : X.E) := by
    intro w
    rw [hdet w]
    have hun : IsUnit (redP w.1 ((LinearEquiv.det ((κ' w)⁻¹).1 : X.Eˣ) : X.E)) :=
      isUnit_reduction_of_integralAt_inv (intAt_det _ ((κ' w)⁻¹).2) (intAt_det_inv _ ((κ' w)⁻¹).2) (Units.ne_zero _)
    have e2 := GlobalTheory.TopLaw.rhoT_inv (Ch := Ch) (sel := sel) (mu := mu) (m2 + 1) w (κ' w)⁻¹
    rw [inv_inv] at e2
    rw [e2]
    unfold muAt rhoS
    rw [GlobalTheory.LastSteps.locChar_unit _ _ hun]

  have hchr : (((twLt Ch (m2 + 1 + 1)).chr a.2.1 * (twTt (R := R) sel mu (m2 + 1 + 1)).chr a.2.2 : X.Kˣ) : X.K) =
      ∏ w : rowSG Pr sel mu,
        (if hw : w.1 ∈ Pr.vGs then
          (((twLt Ch (m2 + 1 + 1) ⟨w.1, hw⟩).lam ⟨(a.2.1 : GLG (E := X.E) (n := R.N (m2 + 1 + 1)) (SG := Pr.vGs)) ⟨w.1, hw⟩, a.2.1.2 _ (Set.mem_univ _)⟩ : X.Kˣ) : X.K)
        else
          (((twTt (R := R) sel mu (m2 + 1 + 1) ⟨w.1, (Finset.mem_union.mp w.2).resolve_left hw⟩).lam
              ⟨(a.2.2 : GLQ X.E (R.N (m2 + 1 + 1)) (QE sel (mu : Chr X.F X.E X.K))) ⟨w.1, (Finset.mem_union.mp w.2).resolve_left hw⟩,
                a.2.2.2 _ (Set.mem_univ _)⟩ : X.Kˣ) : X.K)) := by
    rw [prod_uSG_dite hS
      (fun w => (((twLt Ch (m2 + 1 + 1) w).lam ⟨(a.2.1 : GLG (E := X.E) (n := R.N (m2 + 1 + 1)) (SG := Pr.vGs)) w, a.2.1.2 _ (Set.mem_univ _)⟩ : X.Kˣ) : X.K))
      (fun Q => (((twTt (R := R) sel mu (m2 + 1 + 1) Q).lam ⟨(a.2.2 : GLQ X.E (R.N (m2 + 1 + 1)) (QE sel (mu : Chr X.F X.E X.K))) Q,
        a.2.2.2 _ (Set.mem_univ _)⟩ : X.Kˣ) : X.K))]
    rw [Units.val_mul, levFam_chr_apply_coe]
    congr 1
    exact piChar_apply_coe' _ _ a.2.2

  have hper : ∀ w : rowSG Pr sel mu,
      muAt Ch sel mu cst (m2 + 1) w ((LinearEquiv.det a.1.1 : X.Eˣ) : X.E) *
        topDat Ch sel mu cst (m2 + 1) w (inFr (frsF sel mu p w) (frsF sel mu p' w) (a.1.1.toLinearMap ∘ₗ x)) ((frsF sel mu p w).symm (repY Y)) =
      (if hw : w.1 ∈ Pr.vGs then
          (((twLt Ch (m2 + 1 + 1) ⟨w.1, hw⟩).lam ⟨(a.2.1 : GLG (E := X.E) (n := R.N (m2 + 1 + 1)) (SG := Pr.vGs)) ⟨w.1, hw⟩, a.2.1.2 _ (Set.mem_univ _)⟩ : X.Kˣ) : X.K)
        else
          (((twTt (R := R) sel mu (m2 + 1 + 1) ⟨w.1, (Finset.mem_union.mp w.2).resolve_left hw⟩).lam
              ⟨(a.2.2 : GLQ X.E (R.N (m2 + 1 + 1)) (QE sel (mu : Chr X.F X.E X.K))) ⟨w.1, (Finset.mem_union.mp w.2).resolve_left hw⟩,
                a.2.2.2 _ (Set.mem_univ _)⟩ : X.Kˣ) : X.K)) *
        topDat Ch sel mu cst (m2 + 1) w (inFr (frsF sel mu p w) (frsF sel mu p' w) x) ((frsF sel mu p w).symm (repY Y)) := by
    intro w
    rw [hmu w, hF w]
    have hFst : ∀ z, z ∈ localization₂ w.1.asIdeal p.deco.1.N → (frsF sel mu p w).symm z ∈ stdAt X.E (R.N (m2 + 1)) w.1 := by
      intro z hz
      apply (frsF_isFr sel mu p w _).1
      rw [LinearEquiv.apply_symm_apply]
      exact hz
    by_cases hw : w.1 ∈ Pr.vGs
    · rw [dite_eq_left hw]
      obtain ⟨hne, -, hqm⟩ := ybSet_props2 sel mu cst hY w hw
      have hr0 := representative_mem hne
      have hq : ((qOf w.1 : ℕ) : X.E) • (frsF sel mu p w).symm (repY Y) ∈ stdAt X.E (R.N (m2 + 1)) w.1 := by
        rw [← LinearEquiv.map_smul]
        exact hFst _ (hqm _ hr0)
      have key := topDat_law hc hn hLaw hRow w hw 1 ⟨(a.2.1 : GLG (E := X.E) (n := R.N (m2 + 1 + 1)) (SG := Pr.vGs)) ⟨w.1, hw⟩, a.2.1.2 _ (Set.mem_univ _)⟩
        1 (κ' w) (fun z _ => by simp) (hκr' w hw) (ciQ_notMem_sq hX hPr hw)
        (inFr (frsF sel mu p w) (frsF sel mu p' w) x) ((frsF sel mu p w).symm (repY Y)) ((frsF sel mu p w).symm (repY Y)) (by simp) hq
      have h1 : rhoS Ch sel mu (m2 + 1) w ((LinearEquiv.det ((1 : ↥(GLint X.E (R.N (m2 + 1)) w.1)) : Sp X.E (R.N (m2 + 1)) ≃ₗ[X.E] Sp X.E (R.N (m2 + 1))) : X.Eˣ) : X.E) = 1 := by
        simp [rhoS, LocE.unitV, redP_one]
      rw [h1, one_mul, map_one, inv_one, Units.val_one, mul_one] at key
      exact key
    · rw [dite_eq_right hw]
      obtain ⟨hne, hqm⟩ := coupling_index_scaled_mem_local sel mu cst hY w hw
      have hr0 := representative_mem hne
      have hq : ((qOf w.1 : X.E) ^ cst.M) • (frsF sel mu p w).symm (repY Y) ∈ stdAt X.E (R.N (m2 + 1)) w.1 := by
        rw [← LinearEquiv.map_smul]
        exact hFst _ (hqm _ hr0)
      have hQw := (Finset.mem_union.mp w.2).resolve_left hw
      have hc' : (κ' w)⁻¹ ∈ (twTt (R := R) sel mu (m2 + 1 + 1) ⟨w.1, hQw⟩).H := by
        rw [hκQ' w hw, inv_inv]
        exact a.2.2.2 _ (Set.mem_univ _)
      have key := GlobalTheory.T.twTt_k1Depth_twice_m Ch sel mu cst w hw (κ' w) hc' (inFr (frsF sel mu p w) (frsF sel mu p' w) x) ((frsF sel mu p w).symm (repY Y))
        hm hc (hU w.1 hQw) (hL.depthQ w hw) hMd hq
      have e4 : (⟨(κ' w)⁻¹, hc'⟩ : ↥(twTt (R := R) sel mu (m2 + 1 + 1) ⟨w.1, hQw⟩).H) =
          ⟨(a.2.2 : GLQ X.E (R.N (m2 + 1 + 1)) (QE sel (mu : Chr X.F X.E X.K))) ⟨w.1, hQw⟩, a.2.2.2 _ (Set.mem_univ _)⟩ :=
        Subtype.ext (by show (κ' w)⁻¹ = _; rw [hκQ' w hw, inv_inv])
      rw [e4] at key
      exact key
  rw [hchr]
  have := prod_mul_eq_of_forall_cross_mul_eq _ _ _ _ (phiT X.K p.deco.1 p'.deco.1 x) hper
  linear_combination this

end GlobalTheory.StabTopLaw
end
end
