module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle004
public import Development.AbelianVarietyTheory.Counterexamples.NonGaloisSurvey.Bundle002
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MkMemAdmissibleAtIffCocycle
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle546
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle547
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle362
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.CharFil
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle008
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle009
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle001
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GaloisRepOfPolarizedCuspidal
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.UpperTriangularPlaces.SafeUGap
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.RealCusp
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Newform
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.BaseChangeUnits.IsAutQ
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
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.GalOfCusp
open UpperTheory.V UpperTheory.V.Af

theorem UpperTheory.V.Af.jumpsOpen {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime]
    {n : ℕ} (m : Fin n → ℤ) (r : G F Ω →* GL (Fin n) (Qbar l)) (hr : Continuous r) (A : ValuationSubring Ω)
    {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
    (Bw : LocBridge l F Ω (Dec (F := F) A) O) (hj : Induces Bw) (κ : Fin n → ↥(Dec (F := F) A) →* (Qbar l)ˣ)
    (H : Subgroup (G F Ω)) (hH : IsOpen (H : Set (G F Ω))) (hfl : IsFlagOn r (Dec (F := F) A) κ)
    (hI : ∀ i (s : ↥(Dec (F := F) A)), (s : G F Ω) ∈ H ⊓ Ine (F := F) A → κ i s = cycBar F Ω l s ^ m i)
    (τ : F →+* Qbar l) (J : Multiset ℤ) (hJ : IsJumpsAt (Loc.PP l) Bw (r.comp (Dec (F := F) A).subtype) τ J) :
    J = Finset.univ.val.map fun i => -m i := by
  have char_mult (K L : FinExt l) (κ : ↥(GK K) →* (↥L.1)ˣ) (hκ : Continuous fun g => (κ g : ↥L.1)) (w : ℤ)
      (hw : Loc.HasWeight (GK K).subtype κ w) (hd : IsDR ((Loc.PP l).PD K) (Formalism.WeaklyAdmissibleFiltrations.charRep κ))
      (τ : ↥K.1 →ₐ[ℚ_[l]] ↥L.1) (a : ℤ) : multV ((Loc.PP l).PD K) (Formalism.WeaklyAdmissibleFiltrations.charRep κ) τ a = if a = -w then 1 else 0 := by
    have := L.2
    have := K.2
    have : IsModuleTopology ℚ_[l] ↥L.1 := isModuleTopologyOfFiniteDimensional
    obtain ⟨T⟩ := Loc.tiedP l
    have hφ : Topology.IsOpenEmbedding (GK K).subtype :=
      (IntermediateField.fixingSubgroup_isOpen K.1).isOpenEmbedding_subtypeVal
    have h := (Loc.charFil (GK K).subtype hφ κ hκ w hw).2
    have hF : ∀ i, Loc.FilT ↥L.1 ↥L.1 i = FilV ((Loc.PP l).PD K) (LL := ↥L.1) (V := ↥L.1) i := fun i => by
      have : (((Loc.PP l).PD (Loc.botExt l)).Fil i).restrictScalars ℚ_[l] =
          (((Loc.PP l).PD K).Fil i).restrictScalars ℚ_[l] := SetLike.coe_injective ((Loc.PP l).PD_Fil _ _ i)
      unfold Loc.FilT FilV
      rw [this]
    have hD : Loc.Ddr (GK K).subtype (Loc.chRep κ) = DdR ((Loc.PP l).PD K) (Formalism.WeaklyAdmissibleFiltrations.charRep κ) := by
      unfold Loc.Ddr DdR
      refine iInf_congr fun g => ?_
      have h2 : actVdR ((Loc.PP l).PD K) (Formalism.WeaklyAdmissibleFiltrations.charRep κ) g = Loc.actD (GK K).subtype (Loc.chRep κ) g := by
        unfold actVdR Loc.actD
        congr 1
        exact LinearMap.ext fun z => (Loc.PP l).PD_actdR K g z
      rw [h2]
    simp only [Loc.FilD, hF, hD] at h
    have hr := (((GlobalTheory.Per.Components.components_finrank l _ _ T K L _ (Formalism.WeaklyAdmissibleFiltrations.charRep κ)).1 τ).2.2 hd).trans
      (Module.finrank_self _)
    have hle : DdRE ((Loc.PP l).PD K) (Formalism.WeaklyAdmissibleFiltrations.charRep κ) τ ≤ DdR ((Loc.PP l).PD K) (Formalism.WeaklyAdmissibleFiltrations.charRep κ) := inf_le_left
    set_option synthInstance.maxHeartbeats 200000 in
    have h1 : ∀ i, i ≤ -w → Module.finrank ↥L.1 ↥(FildR ((Loc.PP l).PD K) (Formalism.WeaklyAdmissibleFiltrations.charRep κ) τ i) = 1 := fun i hi => by
      rw [FildR, inf_eq_left.2 (hle.trans (inf_eq_left.1 ((h i).1 hi))), hr]
    set_option synthInstance.maxHeartbeats 200000 in
    have h0 : ∀ i, -w < i → Module.finrank ↥L.1 ↥(FildR ((Loc.PP l).PD K) (Formalism.WeaklyAdmissibleFiltrations.charRep κ) τ i) = 0 := fun i hi => by
      rw [FildR, le_bot_iff.1 ((inf_le_inf_right _ hle).trans ((h i).2 hi).le), finrank_bot]
    unfold multV
    rcases lt_trichotomy a (-w) with ha | ha | ha
    · rw [h1 a ha.le, h1 (a + 1) ha, ite_eq_right ha.ne]; simp
    · rw [h1 a ha.le, h0 (a + 1) (by omega), ite_eq_left ha]; simp
    · rw [h0 a ha, h0 (a + 1) (by omega), ite_eq_right ha.ne']; simp

  have flag_mult (K L : FinExt l) (n : ℕ) : ∀ (ρ : Representation ↥L.1 ↥(GK K) (Fin n → ↥L.1))
      (M : ↥(GK K) → Matrix (Fin n) (Fin n) ↥L.1) (κ : Fin n → ↥(GK K) →* (↥L.1)ˣ),
      (∀ g x, ρ g x = (M g).mulVec x) → (∀ g i j, j < i → M g i j = 0) → (∀ g i, M g i i = κ i g) →
      IsDR ((Loc.PP l).PD K) ρ → (∀ i, IsDR ((Loc.PP l).PD K) (Formalism.WeaklyAdmissibleFiltrations.charRep (κ i))) ∧
        ∀ τ a, multV ((Loc.PP l).PD K) ρ τ a = ∑ i, multV ((Loc.PP l).PD K) (Formalism.WeaklyAdmissibleFiltrations.charRep (κ i)) τ a := by
    obtain ⟨T⟩ := Loc.tiedP l
    induction n with
    | zero =>
      intro ρ M κ _ _ _ _
      refine ⟨fun i => i.elim0, fun τ a => ?_⟩
      have : Subsingleton (TensorProduct ℚ_[l] (Fin 0 → ↥L.1) (Loc.PP l).R.BdR) := inferInstance
      simp [multV, Module.finrank_zero_of_subsingleton]
    | succ n ih =>
      intro ρ M κ hρ hM hκ hd
      let ι : ↥L.1 →ₗ[↥L.1] (Fin (n + 1) → ↥L.1) := LinearMap.single _ (fun _ => ↥L.1) 0
      let π : (Fin (n + 1) → ↥L.1) →ₗ[↥L.1] (Fin n → ↥L.1) := LinearMap.funLeft _ _ Fin.succ
      let M' : ↥(GK K) → Matrix (Fin n) (Fin n) ↥L.1 := fun g => (M g).submatrix Fin.succ Fin.succ
      have hπ : ∀ g x, π (ρ g x) = (M' g).mulVec (π x) := fun g x => by
        funext i
        simp [π, M', hρ, LinearMap.funLeft_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
          hM g i.succ 0 (Fin.succ_pos i)]
      have hs : Function.Surjective π := LinearMap.funLeft_surjective_of_injective _ _ _ (Fin.succ_injective n)
      let ρ' : Representation ↥L.1 ↥(GK K) (Fin n → ↥L.1) :=
        { toFun := fun g => Matrix.toLin' (M' g)
          map_one' := LinearMap.ext fun y => by
            obtain ⟨x, rfl⟩ := hs y
            rw [Matrix.toLin'_apply, ← hπ, map_one]; rfl
          map_mul' := fun g h => LinearMap.ext fun y => by
            obtain ⟨x, rfl⟩ := hs y
            rw [mul_apply_eq_comp, Matrix.toLin'_apply, Matrix.toLin'_apply, Matrix.toLin'_apply, ← hπ, ← hπ, ← hπ,
              map_mul]; rfl }
      obtain ⟨d0, d2, hm⟩ := GlobalTheory.Per.ExactMult.exact_hodge_add l _ _ T K L _ (Formalism.WeaklyAdmissibleFiltrations.charRep (κ 0)) _ ρ _ ρ' ι π
        (fun g x => by
          funext i
          rw [hρ]
          refine Fin.cases ?_ (fun i => ?_) i
          · simp [ι, Formalism.WeaklyAdmissibleFiltrations.charRep, hκ]
          · simp [ι, Formalism.WeaklyAdmissibleFiltrations.charRep, hM g i.succ 0 (Fin.succ_pos i)])
        hπ (fun x y h => by simpa [ι] using congrFun h 0) hs
        (by
          ext x
          simp only [LinearMap.mem_range, LinearMap.mem_ker]
          constructor
          · rintro ⟨y, rfl⟩
            funext i
            simp [ι, π, LinearMap.funLeft_apply]
          · intro h
            refine ⟨x 0, funext fun i => Fin.cases ?_ (fun i => ?_) i⟩
            · simp [ι]
            · simpa [ι, π, LinearMap.funLeft_apply] using (congrFun h i).symm) hd
      obtain ⟨e1, e2⟩ := ih ρ' M' (fun i => κ i.succ) (fun g x => rfl)
        (fun g i j h => hM g _ _ (Fin.succ_lt_succ_iff.2 h)) (fun g i => hκ g _) d2
      refine ⟨fun i => Fin.cases d0 e1 i, fun τ a => ?_⟩
      rw [(hm τ a).2.1, Fin.sum_univ_succ, e2]
  obtain ⟨g, hg⟩ := hfl
  obtain ⟨L, r', hL, hd, τ', -, hc⟩ := (GlobalTheory.ConjLocal.local_conj l (Loc.PP l) F Ω O _ Bw n _
    ((MulAut.conj g).toMonoidHom.comp (r.comp (Dec (F := F) A).subtype)) g (fun _ => rfl)).2.2.2 τ J hJ
  have he : ∀ s i j, ((r' s i j : ↥L.1) : Om l) = (g * r s * g⁻¹ : GL (Fin n) (Om l)) i j := fun s i j =>
    congrArg (fun f : ↥(Dec (F := F) A) →* GL (Fin n) (Om l) => (f s).val i j) hL.2
  have hκ : ∀ s i, ((r' s i i : ↥L.1) : Om l) = κ i s := fun s i => (he s i i).trans ((hg s).2 i)
  let κ' : Fin n → ↥(GK Bw.Kw) →* (↥L.1)ˣ := fun i => MonoidHom.toHomUnits
    { toFun := fun s => r' (Bw.e.symm s) i i
      map_one' := by simp
      map_mul' := fun s t => Subtype.ext (by
        rw [IntermediateField.coe_mul, hκ, hκ, hκ, map_mul, map_mul, Units.val_mul]) }
  have hκ' : ∀ i s, ((κ' i s : ↥L.1) : Om l) = κ i (Bw.e.symm s) := fun i s => hκ _ _
  obtain ⟨d, hm⟩ := flag_mult Bw.Kw L n (Bw.repE L r') (fun s => (r' (Bw.e.symm s)).val) κ' (fun _ _ => rfl)
    (fun s i j h => Subtype.ext ((he _ i j).trans ((hg _).1 i j h))) (fun _ _ => rfl)
    (by rw [IsDR, Module.finrank_fin_fun]; exact hd)
  let U : Subgroup ↥(GK Bw.Kw) := H.comap ((Dec (F := F) A).subtype.comp Bw.e.symm.toMonoidHom)
  have hU : IsOpen (U : Set ↥(GK Bw.Kw)) := hH.preimage (continuous_subtype_val.comp Bw.e_symm_cont)
  have hcm : ∀ (s : ↥(GK Bw.Kw)) x, (s : GQ l) (Bw.j x) = Bw.j ((Bw.e.symm s : G F Ω) x) := fun s x => by
    rw [← Bw.e_comm, MulEquiv.apply_symm_apply]
  have key : ∀ i a, multV ((Loc.PP l).PD Bw.Kw) (Formalism.WeaklyAdmissibleFiltrations.charRep (κ' i)) τ' a = if a = -m i then 1 else 0 := fun i a => by
    refine char_mult Bw.Kw L (κ' i) (continuous_induced_rng.2 ?_) (m i) ⟨U, hU, fun s hs hq => ?_⟩ (d i) τ' a
    · have h1 : Continuous fun s : ↥(GK Bw.Kw) => g * r (Bw.e.symm s) * g⁻¹ :=
        (continuous_const.mul (hr.comp (continuous_subtype_val.comp Bw.e_symm_cont))).mul continuous_const
      exact ((Units.continuous_val.comp h1).matrix_elem i i).congr fun s => (he _ i i).symm
    · have hine : (Bw.e.symm s : G F Ω) ∈ Ine (F := F) A := by
        refine ⟨(Bw.e.symm s).2, fun x hx => ?_⟩
        rw [hj.valuation_lt_one_iff, map_sub, ← hcm]
        exact ((Loc.iqBasic l).2.2.1 _).1 hq _ ((hj x).1 ((A.valuation_le_one_iff x).1 hx))
      have h2 := (GlobalTheory.Survey.CrystallineCharacterRatio.chi_eq_cyc (Loc.PP l) Bw.j _ _ (hcm s)).symm.trans ((Loc.cycFacts l l).2.2 s)
      refine Units.ext (Subtype.ext ?_)
      rw [hκ', hI i (Bw.e.symm s) ⟨hs, hine⟩, Units.val_zpow_eq_zpow_val, Units.val_zpow_eq_zpow_val]
      refine Eq.trans ?_ (map_zpow₀ (algebraMap ↥L.1 (Om l)) _ _).symm
      congr 1
      exact congrArg (algebraMap ℚ_[l] (Om l)) h2
  ext a
  have h := hc a
  rw [LocBridge.multE, hm] at h
  simp only [key] at h
  rw [Multiset.count_map, ← Nat.cast_inj (R := ℤ), h]
  simp [Finset.card_def]
end

section

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Af

section Defs

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]

def IsLevelWD {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 F)} {h : _root_.Formalism.ConjugateSelfDual.IsPlaceOver A w} (M n : ℕ) (x : WD h) : Prop :=
  ∃ (χ : Fin n → _root_.Formalism.ConjugateSelfDual.G F Ω →* ℂˣ) (a : WDRep h (Fin n → ℂ)), (∀ i, KillsMu M (χ i)) ∧ WD.mk a = x ∧ a.N = 0 ∧
    ∀ s : ↥(Ine (F := F) A), a.ρ (ineIncl h s) = Matrix.toLin' (Matrix.diagonal fun i => (χ i s : ℂ))


variable (F) in
def KLoc (w : HeightOneSpectrum (𝓞 F)) (n M : ℕ) : Subgroup (GL (Fin n) (w.adicCompletion F)) :=
  (KLev F n M).comap (locGL F n w)

def LocIsotypic {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin n) (Af F)) V)
    (w : HeightOneSpectrum (𝓞 F)) (σ : SmIrr (GL (Fin n) (w.adicCompletion F))) : Prop :=
  Nontrivial V ∧ ⨆ f : {f : σ.V →ₗ[ℂ] V // ∀ g v, f (σ.ρ g v) = ρ (locGL F n w g) (f v)}, LinearMap.range f.1 = ⊤

def FlagAt {l : ℕ} [Fact l.Prime] {n : ℕ} (M : ℕ) (m : Fin n → ℤ) (r : _root_.Formalism.ConjugateSelfDual.G F Ω →* GL (Fin n) (Qbar l)) (A : ValuationSubring Ω)
    (κ : Fin n → ↥(_root_.ReciprocityTheory.Gal.Dec (F := F) A) →* (Qbar l)ˣ) : Prop :=
  ∃ χ : Fin n → _root_.Formalism.ConjugateSelfDual.G F Ω →* (Qbar l)ˣ, (∀ i, KillsMu M (χ i)) ∧ IsFlagOn r (_root_.ReciprocityTheory.Gal.Dec (F := F) A) κ ∧
    ∀ i (s : ↥(_root_.ReciprocityTheory.Gal.Dec (F := F) A)), (s : _root_.Formalism.ConjugateSelfDual.G F Ω) ∈ Ine (F := F) A → κ i s = cycBar F Ω l s ^ m i * χ i s

end Defs

def WDAway : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime]
    (ι : Qbar l ≃+* ℂ) (n M : ℕ), 1 ≤ M → ∀ (r : _root_.Formalism.ConjugateSelfDual.G F Ω →* GL (Fin n) (Qbar l)), Continuous r →
    ∀ (w : HeightOneSpectrum (𝓞 F)), ((l : ℕ) : 𝓞 F) ∉ w.asIdeal → ∀ (A : ValuationSubring Ω) (h : _root_.Formalism.ConjugateSelfDual.IsPlaceOver A w)
      (χ : Fin n → _root_.Formalism.ConjugateSelfDual.G F Ω →* (Qbar l)ˣ), (∀ i, KillsMu M (χ i)) → IsDiagOn r (Ine (F := F) A) χ →
      ∀ x : WD h, IsWDOf ι r x → IsLevelWD M n x

def WDAbove : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime], l ≠ 2 →
    ∀ (ι : Qbar l ≃+* ℂ) (n M : ℕ), 1 ≤ M → ∀ (m : Fin n → ℤ) (r : _root_.Formalism.ConjugateSelfDual.G F Ω →* GL (Fin n) (Qbar l)), Continuous r →
    ∀ (w : HeightOneSpectrum (𝓞 F)) (A : ValuationSubring Ω) (h : _root_.Formalism.ConjugateSelfDual.IsPlaceOver A w)
      (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
      (Bw : LocBridge l F Ω (_root_.ReciprocityTheory.Gal.Dec (F := F) A) O) (hj : Induces Bw) (κ : Fin n → ↥(_root_.ReciprocityTheory.Gal.Dec (F := F) A) →* (Qbar l)ˣ),
      FlagAt M m r A κ → IsPstAt (Loc.PP l) Bw (r.comp (_root_.ReciprocityTheory.Gal.Dec (F := F) A).subtype) →
      ((∀ i j, κ i ≠ κ j * (cycBar F Ω l).comp (_root_.ReciprocityTheory.Gal.Dec (F := F) A).subtype) ∨ PotCrysAt r A) →
      IsLevelWD M n (wdAt (Loc.PP l) ι Bw h hj (r.comp (_root_.ReciprocityTheory.Gal.Dec (F := F) A).subtype))

def JumpsAbove : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime], l ≠ 2 →
    ∀ (n M : ℕ), 1 ≤ M → ∀ (m : Fin n → ℤ) (r : _root_.Formalism.ConjugateSelfDual.G F Ω →* GL (Fin n) (Qbar l)), Continuous r →
    ∀ (w : HeightOneSpectrum (𝓞 F)) (A : ValuationSubring Ω), _root_.Formalism.ConjugateSelfDual.IsPlaceOver A w →
    ∀ (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
      (Bw : LocBridge l F Ω (_root_.ReciprocityTheory.Gal.Dec (F := F) A) O), Induces Bw → ∀ (κ : Fin n → ↥(_root_.ReciprocityTheory.Gal.Dec (F := F) A) →* (Qbar l)ˣ),
      FlagAt M m r A κ → ∀ (τ : F →+* Qbar l) (J : Multiset ℤ),
      IsJumpsAt (Loc.PP l) Bw (r.comp (_root_.ReciprocityTheory.Gal.Dec (F := F) A).subtype) τ J → J = Finset.univ.val.map fun i => -m i

def LocFixed : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (n M : ℕ), 1 ≤ M →
    ∀ (w : HeightOneSpectrum (𝓞 F)) (A : ValuationSubring Ω) (h : _root_.Formalism.ConjugateSelfDual.IsPlaceOver A w)
      (rc : IrrGL (k := w.adicCompletion F) → WD h), IsRec h rc → ∀ σ : SmIrr (GL (Fin n) (w.adicCompletion F)),
      IsLevelWD M n (rc (algNorm σ)) → HasFixed σ.ρ (KLoc F w n M)

def GlobFixed : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (n M : ℕ), 1 ≤ M → ∀ (V : Type) [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (GL (Fin n) (Af F)) V), GlobalTheory.PRep.IsSmooth ρ →
    (∀ w, ∃ σ, LocIsotypic ρ w σ ∧ HasFixed σ.ρ (KLoc F w n M)) → HasFixed ρ (KLev F n M)

def LocCompC : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (n : ℕ) (π : CuspSub E n) (w : HeightOneSpectrum (𝓞 E)),
    (∃ σ, π.IsLocComp w σ) ∧ ∀ σ, π.IsLocComp w σ → LocIsotypic π.finPart w σ

def LocCompR : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (n : ℕ) (π : TR.CuspSub F n) (w : HeightOneSpectrum (𝓞 F)),
    (∃ σ, π.IsLocComp w σ) ∧ ∀ σ, π.IsLocComp w σ → LocIsotypic π.finPart w σ

def SatLoc : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (n : ℕ) (w : HeightOneSpectrum (𝓞 F)) (σ : SmIrr (GL (Fin n) (w.adicCompletion F))),
    (HasFixed σ.ρ (GlobalTheory.LFun.KGL w (n := n)) → ∃ B, GlobalTheory.LFun.HasSatGL w σ.ρ B) ∧
    ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin n) (Af F)) V), LocIsotypic ρ w σ →
      ∀ B, GlobalTheory.LFun.HasSatGL w (ρ.comp (locGL F n w)) B ↔ GlobalTheory.LFun.HasSatGL w σ.ρ B

def SatFrob : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime]
    (ι : Qbar l ≃+* ℂ) (n : ℕ) (r : _root_.Formalism.ConjugateSelfDual.G F Ω →* GL (Fin n) (Qbar l)), Continuous r →
    ∀ (w : HeightOneSpectrum (𝓞 F)), ((l : ℕ) : 𝓞 F) ∉ w.asIdeal →
    ∀ (σ : SmIrr (GL (Fin n) (w.adicCompletion F))) (B : Multiset ℂˣ), GlobalTheory.LFun.HasSatGL w σ.ρ B →
      (∀ (A : ValuationSubring Ω) (h : _root_.Formalism.ConjugateSelfDual.IsPlaceOver A w) (rc : IrrGL (k := w.adicCompletion F) → WD h), IsRec h rc →
        IsWDOf ι r (rc (algNorm σ))) → FrobEig ι r w (algSat n (normV w) B)

def CrysSlopes : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (p : ℕ) [Fact p.Prime],
    ¬ (p : ℤ) ∣ discr F → ∀ (ι : Qbar p ≃+* ℂ) (n : ℕ) (m : Fin n → ℤ) (r : _root_.Formalism.ConjugateSelfDual.G F Ω →* GL (Fin n) (Qbar p)), Continuous r →
    ∀ (w : HeightOneSpectrum (𝓞 F)) (A : ValuationSubring Ω) (h : _root_.Formalism.ConjugateSelfDual.IsPlaceOver A w)
      (O : Type) [CommRing O] [Algebra ℤ_[p] O] [TopologicalSpace O]
      (Bw : LocBridge p F Ω (_root_.ReciprocityTheory.Gal.Dec (F := F) A) O) (hj : Induces Bw),
      IsCrysAt (Loc.PP p) Bw (r.comp (_root_.ReciprocityTheory.Gal.Dec (F := F) A).subtype) →
      (∀ (τ : F →+* Qbar p) (LL' : FinExt p) (τ' : ↥Bw.Kw.1 →ₐ[ℚ_[p]] ↥LL'.1), IsInduced Bw τ τ' →
        IsJumpsAt (Loc.PP p) Bw (r.comp (_root_.ReciprocityTheory.Gal.Dec (F := F) A).subtype) τ (Finset.univ.val.map fun i => -m i)) →
      ∀ (σ : SmIrr (GL (Fin n) (w.adicCompletion F))) (B : Multiset ℂˣ), GlobalTheory.LFun.HasSatGL w σ.ρ B →
      ∀ rc, IsRec h rc → wdAt (Loc.PP p) ι Bw h hj (r.comp (_root_.ReciprocityTheory.Gal.Dec (F := F) A).subtype) = rc (algNorm σ) →
      ∀ b ∈ algSat n (normV w) B, (∀ a : ℤ, (∀ i, -a ≤ m i) → ‖ι.symm ((normV w : ℂ) ^ a * b⁻¹)‖ ≤ 1) ∧
        ∀ a : ℤ, (∀ i, m i ≤ a) → ‖ι.symm ((normV w : ℂ) ^ a * b)‖ ≤ 1

def WeylC : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (n : ℕ), ∃ c A : ℕ, ∀ m : Fin n → ℤ, StrictAnti m →
    ∀ H : ℕ, (∀ i, |m i| ≤ H) → ∃ Ξ : GlobalTheory.GKCoh.AlgRep E n, (∀ τ, AlgInfChar Ξ τ ((infOf m).map Neg.neg)) ∧ Ξ.d ≤ c * (H + 1) ^ A

end UpperTheory.V.Af
end
end

section

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.GalOfCusp
open scoped Matrix

namespace UpperTheory.V.Af

section admitted

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] {l : ℕ} [Fact l.Prime] {n : ℕ}

def AttR [IsTotallyReal F] (ι : Qbar l ≃+* ℂ) (r : G F Ω →* GL (Fin n) (Qbar l)) (π : TR.CuspSub F n) : Prop :=
  AttachedSys ι r π.HasSat

def IsAutR [IsTotallyReal F] (ι : Qbar l ≃+* ℂ) (r : G F Ω →* GL (Fin n) (Qbar l)) : Prop :=
  ∃ π : TR.CuspSub F n, π.IsRegAlg ∧ AttR ι r π

def DualTw {Γ k : Type} [Group Γ] [Field k] (r : Γ →* GL (Fin n) k) (θ : Γ →* kˣ) : Prop :=
  ∃ P : GL (Fin n) k, ∀ s, (r s : Matrix (Fin n) (Fin n) k)ᵀ * (P : Matrix (Fin n) (Fin n) k) * (r s : Matrix (Fin n) (Fin n) k) =
    (θ s : k) • (P : Matrix (Fin n) (Fin n) k)


omit [NumberField F] in
variable (l) in
def IsCycWt (wt : ℤ) (θ : G F Ω →* (Qbar l)ˣ) : Prop :=
  ∃ (M : ℕ) (χ : G F Ω →* (Qbar l)ˣ), 1 ≤ M ∧ KillsMu M χ ∧ θ = cycBar F Ω l ^ wt * χ


variable (l) in
structure LevelO (M : ℕ) (m : Fin n → ℤ) (r : G F Ω →* GL (Fin n) (Qbar l)) : Prop extends Level l M m r where
  odd : Odd n

structure AdmK [IsCMField F] (ι : Qbar l ≃+* ℂ) (M : ℕ) (m : Fin n → ℤ) (r : G F Ω →* GL (Fin n) (Qbar l)) : Prop where
  irr : IsIrr r
  aut : IsAutCsd ι r
  level : LevelO l M m r

structure AdmR [IsTotallyReal F] (ι : Qbar l ≃+* ℂ) (M : ℕ) (m : Fin n → ℤ) (wt : ℤ)
    (r : G F Ω →* GL (Fin n) (Qbar l)) : Prop where
  irr : IsIrr r
  aut : IsAutQ ι r
  level : Level l M m r
  dual : ∃ θ, IsCycWt l wt θ ∧ DualTw r θ
  safe : Keep.SafeU l M m r

end admitted

structure EigData (n q : ℕ) (m : Fin n → ℤ) (wt : ℤ) where

  S : Type
  fin : Finite S

  β : S → Multiset ℂ
  card : ∀ s, (β s).card = n
  conj : ∀ σ : ℂ ≃+* ℂ, ∃ e : S ≃ S, ∀ s, β (e s) = (β s).map σ
  pure : ∀ s, ∀ b ∈ β s, ‖b‖ = (q : ℝ) ^ ((wt : ℝ) / 2)
  int : ∀ a : ℤ, (∀ i, -a ≤ m i) → ∀ s, ∀ b ∈ β s, IsIntegral ℤ ((q : ℂ) ^ a * b)
  intInv : ∀ a : ℤ, (∀ i, m i ≤ a) → ∀ s, ∀ b ∈ β s, IsIntegral ℤ ((q : ℂ) ^ a * b⁻¹)

def EigData.Classifies {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] {l : ℕ} [Fact l.Prime] {n q : ℕ}
    {m : Fin n → ℤ} {wt : ℤ} (D : EigData n q m wt) (ι : Qbar l ≃+* ℂ) (w : HeightOneSpectrum (𝓞 F))
    (admitted : (G F Ω →* GL (Fin n) (Qbar l)) → Prop) : Prop :=
  ∃ cl : {r // admitted r} → D.S, (∀ r r', cl r = cl r' → RepIso r.1 r'.1) ∧
    ∀ r, FrobEig ι r.1 w ((D.β (cl r)).map (·⁻¹))

def CountK : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [IsCMField K] (n : ℕ), 2 ≤ n → ∃ c A : ℕ,
    ∀ (m : Fin n → ℤ), StrictAnti m → (∀ i, m i + m i.rev = 1 - n) → ∀ H : ℕ, (∀ i, |m i| ≤ H) → ∀ M : ℕ, 1 ≤ M →
    ∀ (p : ℕ) (w : HeightOneSpectrum (𝓞 K)), p.Prime → (p : 𝓞 K) ∈ w.asIdeal → ¬ p ∣ M → ¬ (p : ℤ) ∣ discr K →
      ∃ D : EigData n (normV w) m (1 - n), Nat.card D.S ≤ c * (M * (H + 1)) ^ A ∧
        ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → l ≠ p → ∀ (Ω : Type) [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] (ι : Qbar l ≃+* ℂ),
          D.Classifies (Ω := Ω) ι w (AdmK ι M m)

def CountQ : Prop :=
  ∀ (n : ℕ), 2 ≤ n → ∃ c A : ℕ,
    ∀ (m : Fin n → ℤ) (wt : ℤ), StrictAnti m → (∀ i, m i + m i.rev = wt) → ∀ H : ℕ, (∀ i, |m i| ≤ H) → ∀ M : ℕ, 1 ≤ M →
    ∀ (p : ℕ) (w : HeightOneSpectrum (𝓞 ℚ)), p.Prime → (p : 𝓞 ℚ) ∈ w.asIdeal → ¬ p ∣ M →
      ∃ D : EigData n p m wt, Nat.card D.S ≤ c * (M * (H + 1)) ^ A ∧
        ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → l ≠ p → ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ι : Qbar l ≃+* ℂ),
          D.Classifies (Ω := Ω) ι w (AdmR ι M m wt)

def NewformAutR : Prop :=
  ∀ (k : ℕ), 2 ≤ k → ∀ (f : Newform k) (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω]
    (ι : Qbar l ≃+* ℂ) (W : G ℚ Ω →* GL (Fin 2) (Qbar l)) (j : ℤ), f.Att ι (tw W (cycBar ℚ Ω l ^ j)) → IsAutR ι W

section U3

variable {K Ω : Type} [Field K] [NumberField K] [Field Ω] [Algebra ℚ Ω] [Algebra K Ω] [IsScalarTower ℚ K Ω]
  {l : ℕ} [Fact l.Prime]

structure Adm3 [IsCMField K] (ι : Qbar l ≃+* ℂ) (e N : ℕ) (ρ : G K Ω →* GL (Fin 3) (Qbar l)) : Prop where
  irr : IsIrr ρ
  aut : IsAutCsd ι (tw ρ (cycBar K Ω l)⁻¹)
  level : Level l N ![(e : ℤ), 0, -(e : ℤ)] ρ

def Adm2 (ι : Qbar l ≃+* ℂ) (e M : ℕ) (ρ : G K Ω →* GL (Fin 3) (Qbar l)) : Prop :=
  ∃ W : G ℚ Ω →* GL (Fin 2) (Qbar l), IsIrr W ∧ (∃ f : Newform (2 * e + 1), f.Att ι (tw W (cycBar ℚ Ω l ^ (-(e : ℤ))))) ∧
    Level l M ![(e : ℤ), -(e : ℤ)] W ∧ IsCycWt l 0 (Matrix.GeneralLinearGroup.det.comp W) ∧
    ∃ g : GL (Fin 3) (Qbar l), ∀ s : G K Ω, ((g * ρ s * g⁻¹ : GL (Fin 3) (Qbar l)) : Matrix (Fin 3) (Fin 3) (Qbar l)) =
      !![W (s.restrictScalars ℚ) 0 0, 0, W (s.restrictScalars ℚ) 0 1; 0, 1, 0;
         W (s.restrictScalars ℚ) 1 0, 0, W (s.restrictScalars ℚ) 1 1]

end U3

def eis3 (q e : ℕ) (z : ℂ) : ℂ := ((q : ℂ) ^ e)⁻¹ * z + 1 + (q : ℂ) ^ e * z⁻¹

def eis4 (p e : ℕ) (z₁ z₂ z₃ : ℂ) : ℂ := (p : ℂ) ^ (e + 1) * z₁ + (p : ℂ) ^ e * z₂ + (p : ℂ) * z₃ + 1

def NumberSp4 : Prop :=
  ∃ c A : ℕ, ∀ e : ℕ, 2 ≤ e → ∀ M : ℕ, 1 ≤ M → ∀ (p : ℕ) (w : HeightOneSpectrum (𝓞 ℚ)), p.Prime → (p : 𝓞 ℚ) ∈ w.asIdeal →
    5 ≤ p → ¬ p ∣ M → ∀ k : ℕ, 0 < k → ∀ z₁ z₂ z₃ : ℂ, z₁ ^ k = 1 → z₂ ^ k = 1 → z₃ ^ k = 1 →
    ∃ NN : ℤ, NN ≠ 0 ∧ Real.log |(NN : ℝ)| ≤ c * Nat.totient k * ((M : ℝ) * (e + 1)) ^ A * Real.log p ∧
      ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → l ≠ p → ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ι : Qbar l ≃+* ℂ)
        (B : ValuationSubring Ω), IsPlaceOver B w → ∀ σ : G ℚ Ω, IsFrob B p σ →
        ∀ X : Finset (G ℚ Ω →* GL (Fin 4) (Qbar l)),
          (∀ r ∈ X, AdmR ι M ![(e : ℤ) + 1, e, 1, 0] (e + 1) r) → (∀ r ∈ X, ∀ r' ∈ X, RepIso r r' → r = r') →
          (∀ r ∈ X, (r σ : Matrix (Fin 4) (Fin 4) (Qbar l)).trace ≠ ι.symm (eis4 p e z₁ z₂ z₃)) ∧
          ‖((NN : ℤ) : Qbar l)‖ ≤ ∏ r ∈ X, ‖(r σ : Matrix (Fin 4) (Fin 4) (Qbar l)).trace - ι.symm (eis4 p e z₁ z₂ z₃)‖

section Ad

variable {F₀ F Ω : Type} [Field F₀] [Field F] [Field Ω] [Algebra F₀ F] [Algebra F₀ Ω] [Algebra F Ω] [IsScalarTower F₀ F Ω]
  {k : Type} [Field k] {n : ℕ}

def IsAdOf (r : G F Ω →* GL (Fin n) k) (μ : G F Ω →* kˣ) (ρ : Representation k (G F₀ Ω) (Matrix (Fin n) (Fin n) k)) : Prop :=
  ∃ (c : G F₀ Ω) (P : GL (Fin n) k), (∃ j : Ω →+* ℂ, ∀ x, j (c x) = starRingEnd ℂ (j x)) ∧
    (∀ s s' : G F Ω, s'.restrictScalars F₀ = c * s.restrictScalars F₀ * c⁻¹ →
      (r s : Matrix (Fin n) (Fin n) k)ᵀ * (P : Matrix (Fin n) (Fin n) k) * (r s' : Matrix (Fin n) (Fin n) k) =
        (μ s : k) • (P : Matrix (Fin n) (Fin n) k)) ∧
    (∀ (s : G F Ω) (X : Matrix (Fin n) (Fin n) k), ρ (s.restrictScalars F₀) X =
      (r s : Matrix (Fin n) (Fin n) k) * X * ((r s)⁻¹ : GL (Fin n) k)) ∧
    ∀ X : Matrix (Fin n) (Fin n) k, ρ c X = -((P⁻¹ : GL (Fin n) k) * Xᵀ * (P : Matrix (Fin n) (Fin n) k))

end Ad

def AdVanishK : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [IsCMField K], Module.finrank ℚ K = 2 → ∀ (n : ℕ), 2 ≤ n →
    ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [Algebra K Ω] [IsScalarTower ℚ K Ω] [IsAlgClosure K Ω]
      (ι : Qbar l ≃+* ℂ) (r : G K Ω →* GL (Fin n) (Qbar l)), Continuous r → IsAutCsd ι r →
      IsIrr (r.comp (cycBar K Ω l).ker.subtype) →
      ∀ ρ : Representation (Qbar l) (G ℚ Ω) (Matrix (Fin n) (Fin n) (Qbar l)),
        IsAdOf r (cycBar K Ω l ^ (1 - (n : ℤ))) ρ → BlochKatoSelmerVanishes l ρ

def AdVanishQ : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [IsCMField K], Module.finrank ℚ K = 2 → ∀ (n : ℕ), 2 ≤ n →
    ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [Algebra K Ω] [IsScalarTower ℚ K Ω] [IsAlgClosure K Ω]
      (ι : Qbar l ≃+* ℂ) (r : G ℚ Ω →* GL (Fin n) (Qbar l)) (wt : ℤ) (θ : G ℚ Ω →* (Qbar l)ˣ), Continuous r → IsAutQ ι r →
      IsCycWt l wt θ → DualTw r θ →
      IsIrr ((r.comp (AlgEquiv.restrictScalarsHom ℚ : G K Ω →* G ℚ Ω)).comp (cycBar K Ω l).ker.subtype) →
      ∀ ρ : Representation (Qbar l) (G ℚ Ω) (Matrix (Fin n) (Fin n) (Qbar l)),
        IsAdOf (r.comp (AlgEquiv.restrictScalarsHom ℚ : G K Ω →* G ℚ Ω)) (θ.comp (AlgEquiv.restrictScalarsHom ℚ)) ρ →
        BlochKatoSelmerVanishes l ρ

end UpperTheory.V.Af
end
end
