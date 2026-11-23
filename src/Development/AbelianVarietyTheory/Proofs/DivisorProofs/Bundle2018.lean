module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle055
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1199
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1989
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1968
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompactOpenAddSubgroup
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1770
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianTensorSkewHermitianLatticeOpenCompact
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1883
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle265
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1903
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1344
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle065
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1527
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle315
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsOpenKerOfContinuous
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1287
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WittFrameDarbouxCoordinates
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1978
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Topology.MetricSpace.Ultra.Pi
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts

@[expose] public section

section

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Classical

open scoped GlobalTheory.VacAny
open Topology

noncomputable section
namespace GlobalTheory.VacAvg

def schrL {K : Type} [CommRing K] [Invertible (2 : K)] (ψ : AddChar K ℂ) {κ : Type} [Fintype κ]
    (z : (κ → K) × (κ → K)) : Module.End ℂ ((κ → K) → ℂ) where
  toFun := schr ψ z
  map_add' f g := by funext x; simp only [schr, Pi.add_apply, mul_add]
  map_smul' r f := by funext x; simp only [schr, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

theorem schrL_apply {K : Type} [CommRing K] [Invertible (2 : K)] (ψ : AddChar K ℂ) {κ : Type} [Fintype κ]
    (z : (κ → K) × (κ → K)) (f : (κ → K) → ℂ) : schrL ψ z f = schr ψ z f := rfl

theorem ops_schrL {K : Type} [CommRing K] [Invertible (2 : K)] (ψ : AddChar K ℂ) {κ : Type} [Fintype κ] :
    GlobalTheory.Published.SvN.Ops (fun z z' : (κ → K) × (κ → K) => ψ (⅟(2 : K) * (z.1 ⬝ᵥ z'.2 - z'.1 ⬝ᵥ z.2))) (schrL ψ) := by
  constructor
  · intro v
    funext x
    simp [schrL_apply, schr]
  · intro x y v
    simp only [schrL_apply]
    exact schr_schr ψ x y v

theorem addChar_ne_zero {A : Type} [AddGroup A] (ψ : AddChar A ℂ) (t : A) : ψ t ≠ 0 := by
  intro h
  have := ψ.map_add_eq_mul t (-t)
  rw [add_neg_cancel, AddChar.map_zero_eq_one, h, zero_mul] at this
  exact one_ne_zero this

theorem eventually_schr_fix {F : Type} [Field F] [NumberField F] (v : Pl (F := F)) (ψ : AddChar (Fv F v) ℂ)
    (hψ : Continuous ψ) {κ : Type} [Fintype κ] {f : (κ → Fv F v) → ℂ} (hf : f ∈ SB (κ → Fv F v)) :
    ∀ᶠ z in 𝓝 (0 : (κ → Fv F v) × (κ → Fv F v)), schr ψ z f = f := by
  obtain ⟨U₀, hU₀⟩ := GlobalTheory.HeisLatVac.lc_exists_open_ker ψ hψ
  obtain ⟨K, hK⟩ := GlobalTheory.WeilM.HaarUniq.exists_invariant hf
  have hc : Continuous fun z : ((κ → Fv F v) × (κ → Fv F v)) × (κ → Fv F v) =>
      z.2 ⬝ᵥ z.1.2 + ⅟(2 : Fv F v) * (z.1.1 ⬝ᵥ z.1.2) :=
    (continuous_snd.dotProduct continuous_fst.snd).add
      (continuous_const.mul (continuous_fst.fst.dotProduct continuous_fst.snd))
  have h1 : ∀ᶠ z : (κ → Fv F v) × (κ → Fv F v) in 𝓝 0, ∀ x ∈ tsupport f,
      x ⬝ᵥ z.2 + ⅟(2 : Fv F v) * (z.1 ⬝ᵥ z.2) ∈ (U₀ : Set (Fv F v)) := by
    refine IsCompact.eventually_forall_of_forall_eventually hf.2
      (P := fun (z : (κ → Fv F v) × (κ → Fv F v)) (x : κ → Fv F v) =>
        x ⬝ᵥ z.2 + ⅟(2 : Fv F v) * (z.1 ⬝ᵥ z.2) ∈ (U₀ : Set (Fv F v))) fun x _ => ?_
    refine (U₀.isOpen.preimage hc).mem_nhds ?_
    simpa using U₀.zero_mem
  have h2 : ∀ᶠ z : (κ → Fv F v) × (κ → Fv F v) in 𝓝 0, z.1 ∈ (K : Set (κ → Fv F v)) :=
    (K.isOpen.preimage continuous_fst).mem_nhds K.zero_mem
  filter_upwards [h1, h2] with z hz1 hz2
  funext x
  show ψ (x ⬝ᵥ z.2 + ⅟(2 : Fv F v) * (z.1 ⬝ᵥ z.2)) * f (x + z.1) = f x
  rw [hK z.1 hz2 x]
  by_cases hx : x ∈ tsupport f
  · rw [hU₀ _ (hz1 x hx), one_mul]
  · rw [image_eq_zero_of_notMem_tsupport hx, mul_zero]

theorem tens_sum {F : Type} [Field F] [NumberField F] {R κ ι : Type} (ev : AF F → R) (s : Finset ι) (c : ι → ℂ)
    (g : ι → (κ → R) → ℂ) (r : (κ → AF F) → ℂ) :
    tens ev (∑ q ∈ s, c q • g q) r = ∑ q ∈ s, c q • tens ev (g q) r := by
  funext x
  simp only [tens, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul, mul_assoc]

theorem tens_smul {F : Type} [Field F] [NumberField F] {R κ : Type} (ev : AF F → R) (c : ℂ) (g : (κ → R) → ℂ)
    (r : (κ → AF F) → ℂ) : tens ev (c • g) r = c • tens ev g r := by
  funext x
  simp only [tens, Pi.smul_apply, smul_eq_mul, mul_assoc]

theorem rho_sum {R : Type} [CommRing R] [Invertible (2 : R)] {W : Type} [AddCommGroup W] [Module R W]
    {B : W → W → R} {κ ι : Type} [Fintype κ] (d : Darboux B κ) (ψ : AddChar R ℂ) (γ : W) (s : Finset ι)
    (Φ : ι → (κ → R) → ℂ) : d.rho ψ γ (∑ q ∈ s, Φ q) = ∑ q ∈ s, d.rho ψ γ (Φ q) := by
  funext x
  simp only [Darboux.rho, schr, Finset.sum_apply, Finset.mul_sum]

theorem avg_eigen : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (w : Pl (F := F)) (Ψ : (Fin a' × Fin (a + a') → AF F) → ℂ), Ψ ∈ schA F (Fin a' × Fin (a + a')) →
    (∀ γ ∈ latAtV G.V' G.W w, ∀ c : ℂ, Acts (evFin F w) (G.M'.co.rho B.ψ γ) (G.M'.vac w) (c • G.M'.vac w) →
      G.M'.co.rho B.ψ γ Ψ = c • Ψ) →
    ∀ (m : ℕ) (f : Fin m → SInf F (Fin a' × Fin (a + a'))) (φ : Fin m → ∀ v : Pl (F := F), (Fin a' × Fin (a + a') → Fv F v) → ℂ),
    (∀ i v, φ i v ∈ SB (Fin a' × Fin (a + a') → Fv F v)) →
    (∀ i, ∀ᶠ v in Filter.cofinite, φ i v = Set.indicator {x | ∀ j, x j ∈ v.adicCompletionIntegers F} 1) →
    Ψ = ∑ i, pure (f i) (φ i) →
    ∃ g : Fin m → (Fin a' × Fin (a + a') → Fv F w) → ℂ, (∀ i, g i ∈ SB (Fin a' × Fin (a + a') → Fv F w)) ∧
      (∀ i, ∀ γ ∈ latAtV G.V' G.W w, ∀ c : ℂ, Acts (evFin F w) (G.M'.co.rho B.ψ γ) (G.M'.vac w) (c • G.M'.vac w) →
        Acts (evFin F w) (G.M'.co.rho B.ψ γ) (g i) (c • g i)) ∧
      Ψ = ∑ i, pure (f i) (Function.update (φ i) w (g i)) := by
  intro _ F E _ _ _ _ _ σ B a a' G X om om' hT w Ψ _ hyp m f φ hSB hstd hsum
  classical
  have hψc : Continuous (GlobalTheory.LatVac.psiAt B.ψ w) := GlobalTheory.SchrSB.continuous_psiAt B.ψ hT.base.std.1 w
  obtain ⟨hvSB, hv0, θ, -, hθ⟩ := hT.geo.hM'.vac w
  have hat : ∀ γ ∈ latAtV G.V' G.W w, At (evFin F w) γ := (GlobalTheory.LatVac.latAtV_at_stable G.V' G.W w).1
  set L := schrL (κ := Fin a' × Fin (a + a')) (GlobalTheory.LatVac.psiAt B.ψ w) with hL
  set vac := G.M'.vac w with hvac
  set Λ := (latAtV G.V' G.W w).map (GlobalTheory.LatVac.locCo G.M'.co w) with hΛ
  obtain ⟨-, hΛc⟩ := GlobalTheory.LatOpenCpt.main σ B G.V' G.W _ _ _ _ hT.geo.hV' hT.geo.hW G.M' hT.geo.hM'.rat w
  have hAct : ∀ γ ∈ latAtV G.V' G.W w, ∀ φ₀ : (Fin a' × Fin (a + a') → Fv F w) → ℂ,
      Acts (evFin F w) (G.M'.co.rho B.ψ γ) φ₀ (L (GlobalTheory.LatVac.locCo G.M'.co w γ) φ₀) :=
    fun γ hγ φ₀ => GlobalTheory.VacBridge.rho_acts_locCo G.M'.co B.ψ w γ (hat γ hγ) φ₀
  have huniq : ∀ γ ∈ latAtV G.V' G.W w, ∀ c₀ : ℂ, Acts (evFin F w) (G.M'.co.rho B.ψ γ) vac (c₀ • vac) →
      L (GlobalTheory.LatVac.locCo G.M'.co w γ) vac = c₀ • vac := fun γ hγ c₀ h =>
    GlobalTheory.TensUniq.eq_of_tens_eq w vac _ _ hvSB fun r hr => (hAct γ hγ vac r hr).symm.trans (h r hr)
  have hinj : ∀ e e' : ℂ, e • vac = e' • vac → e = e' := fun e e' h => smul_left_injective ℂ hv0 h
  have hex : ∀ z ∈ Λ, ∃ e : ℂ, L z vac = e • vac := by
    rintro _ ⟨γ, hγ, rfl⟩
    exact ⟨_, huniq γ hγ _ (hθ γ hγ)⟩
  let α : (Fin a' × Fin (a + a') → Fv F w) × (Fin a' × Fin (a + a') → Fv F w) → ℂ :=
    fun z => if h : ∃ e : ℂ, L z vac = e • vac then h.choose else 1
  have hαspec : ∀ z, (∃ e : ℂ, L z vac = e • vac) → L z vac = α z • vac := fun z h => by
    show _ = (if h : ∃ e : ℂ, L z vac = e • vac then h.choose else 1) • vac
    rw [dite_eq_left h]
    exact h.choose_spec
  let c : (Fin a' × Fin (a + a') → Fv F w) × (Fin a' × Fin (a + a') → Fv F w) →
      (Fin a' × Fin (a + a') → Fv F w) × (Fin a' × Fin (a + a') → Fv F w) → ℂ :=
    fun z z' => GlobalTheory.LatVac.psiAt B.ψ w (⅟(2 : Fv F w) * (z.1 ⬝ᵥ z'.2 - z'.1 ⬝ᵥ z.2))
  have hops : GlobalTheory.Published.SvN.Ops c L := ops_schrL _
  have hαne : ∀ z ∈ Λ, α z ≠ 0 := by
    intro z hz h0
    have h1 := hops.mul (-z) z vac
    rw [hαspec z (hex z hz), h0, zero_smul, map_zero, neg_add_cancel, hops.zero] at h1
    exact hv0 ((smul_eq_zero.1 h1.symm).resolve_left (addChar_ne_zero _ _))
  have hsplit : GlobalTheory.Published.SvN.Splits c Λ α := by
    refine ⟨hαne, fun x hx y hy => hinj _ _ ?_⟩
    have h1 := hops.mul x y vac
    rw [hαspec y (hex y hy), map_smul, hαspec x (hex x hx), hαspec (x + y) (hex _ (Λ.add_mem hx hy)), smul_smul,
      smul_smul] at h1
    rw [mul_comm (α x)]
    exact h1
  have hfix : ∀ᶠ z in 𝓝 (0 : (Fin a' × Fin (a + a') → Fv F w) × (Fin a' × Fin (a + a') → Fv F w)),
      L z vac = vac ∧ ∀ i, L z (φ i w) = φ i w :=
    (eventually_schr_fix w _ hψc hvSB).and (Filter.eventually_all.2 fun i => eventually_schr_fix w _ hψc (hSB i w))
  obtain ⟨U, hU⟩ := NonarchimedeanAddGroup.is_nonarchimedean _ hfix
  have hUα : ∀ u ∈ U.toAddSubgroup, α u = 1 := fun u hu =>
    hinj _ _ (by rw [← hαspec u ⟨1, by rw [one_smul]; exact (hU hu).1⟩, one_smul]; exact (hU hu).1)
  have hfin : Finite (Λ ⧸ U.toAddSubgroup.addSubgroupOf Λ) :=
    GlobalTheory.Published.SvN.finite_quot Λ U.toAddSubgroup U.mem_nhds_zero hΛc subset_rfl
  letI := Fintype.ofFinite (Λ ⧸ U.toAddSubgroup.addSubgroupOf Λ)
  obtain ⟨avg, havg⟩ : ∃ avg : Fin m → (Fin a' × Fin (a + a') → Fv F w) → ℂ, ∀ i,
      avg i = ∑ q : Λ ⧸ U.toAddSubgroup.addSubgroupOf Λ, (α q.out.1)⁻¹ • L q.out.1 (φ i w) := ⟨_, fun _ => rfl⟩
  have heig : ∀ i, ∀ z ∈ Λ, L z (avg i) = α z • avg i := fun i z hz => by
    rw [havg i]
    exact GlobalTheory.Published.SvN.average hops hsplit U.toAddSubgroup hUα (φ i w) (fun u hu => (hU hu).2 i) z hz
  set N := Fintype.card (Λ ⧸ U.toAddSubgroup.addSubgroupOf Λ) with hN
  have hN0 : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  choose γq hγq hγqe using fun q : Λ ⧸ U.toAddSubgroup.addSubgroupOf Λ => AddSubgroup.mem_map.1 q.out.2
  choose r hr1 hr2 using fun i => GlobalTheory.PureFactor.exists_rest_factor w (f i) (φ i) (hstd i)
  have hpure : ∀ i, pure (f i) (φ i) = tens (evFin F w) (φ i w) (r i) := fun i => by
    rw [hr2, Function.update_eq_self]
  have hRest : ∀ i, Rest (evFin F w) (φ i w) (r i) := fun i =>
    ⟨hr1 i, hpure i ▸ GlobalTheory.TensUniq.pure_mem_schA (f i) (φ i) (hSB i) (hstd i)⟩
  have hΨ' : Ψ = ∑ i, tens (evFin F w) (φ i w) (r i) := by
    rw [hsum]; exact Finset.sum_congr rfl fun i _ => hpure i
  have hqΨ : ∀ q : Λ ⧸ U.toAddSubgroup.addSubgroupOf Λ, G.M'.co.rho B.ψ (γq q) Ψ = α q.out.1 • Ψ := fun q =>
    hyp _ (hγq q) _ (by
      have := hAct _ (hγq q) vac
      rwa [hγqe q, hαspec _ (hex _ q.out.2)] at this)
  have hqΨ2 : ∀ q : Λ ⧸ U.toAddSubgroup.addSubgroupOf Λ,
      G.M'.co.rho B.ψ (γq q) Ψ = ∑ i, tens (evFin F w) (L q.out.1 (φ i w)) (r i) := fun q => by
    rw [hΨ', rho_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hAct _ (hγq q) (φ i w) (r i) (hRest i), hγqe q]
  have e1 : ∑ q : Λ ⧸ U.toAddSubgroup.addSubgroupOf Λ, (α q.out.1)⁻¹ • G.M'.co.rho B.ψ (γq q) Ψ = (N : ℂ) • Ψ := by
    calc ∑ q : Λ ⧸ U.toAddSubgroup.addSubgroupOf Λ, (α q.out.1)⁻¹ • G.M'.co.rho B.ψ (γq q) Ψ
          = ∑ q : Λ ⧸ U.toAddSubgroup.addSubgroupOf Λ, Ψ :=
          Finset.sum_congr rfl fun q _ => by rw [hqΨ q, smul_smul, inv_mul_cancel₀ (hαne _ q.out.2), one_smul]
      _ = (N : ℂ) • Ψ := by rw [Finset.sum_const, Finset.card_univ, Nat.cast_smul_eq_nsmul]
  have e2 : ∑ q : Λ ⧸ U.toAddSubgroup.addSubgroupOf Λ, (α q.out.1)⁻¹ • G.M'.co.rho B.ψ (γq q) Ψ =
      ∑ i, tens (evFin F w) (avg i) (r i) := by
    simp only [hqΨ2, Finset.smul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [havg i, tens_sum]
  have hgSB : ∀ i, (N : ℂ)⁻¹ • avg i ∈ SB (Fin a' × Fin (a + a') → Fv F w) := fun i => by
    rw [havg i]
    exact (SB _).smul_mem _ (Submodule.sum_mem _ fun q _ => (SB _).smul_mem _
      (GlobalTheory.SchrSB.schr_mem_SB B.ψ hT.base.std.1 w _ _ (hSB i w)))
  refine ⟨fun i => (N : ℂ)⁻¹ • avg i, hgSB, fun i γ hγ c₀ hc => ?_, ?_⟩
  · have hz : GlobalTheory.LatVac.locCo G.M'.co w γ ∈ Λ := AddSubgroup.mem_map_of_mem _ hγ
    have e := huniq γ hγ c₀ hc
    rw [hαspec _ (hex _ hz)] at e
    have hc₀ := hinj _ _ e
    have := hAct γ hγ ((N : ℂ)⁻¹ • avg i)
    rwa [map_smul, heig i _ hz, hc₀, smul_comm] at this
  · calc Ψ = (N : ℂ)⁻¹ • ((N : ℂ) • Ψ) := by rw [smul_smul, inv_mul_cancel₀ hN0, one_smul]
      _ = _ := by
        rw [← e1, e2, Finset.smul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← tens_smul, hr2]

end GlobalTheory.VacAvg
end
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.KSplit
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.DblScalDet

open GlobalTheory.DblScal
open scoped Matrix

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem udat_mul {σ : E →ₐ[F] E} {d : ℕ} {J : Matrix (Fin d) (Fin d) E} {R : Type} [Zero R] {ev : AF F → R}
    {p q : UD σ J} (hp : p ∈ UDAt σ J ev) (hq : q ∈ UDAt σ J ev) : p * q ∈ UDAt σ J ev := by
  intro u hu
  have e : ((((p * q : UD σ J) : GL (Fin d ⊕ Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))) - 1 =
      ((((p : UD σ J) : GL (Fin d ⊕ Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) - 1) *
        (((q : UD σ J) : GL (Fin d ⊕ Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) +
      ((((q : UD σ J) : GL (Fin d ⊕ Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) - 1) := by
    simp [sub_mul]
  rw [e, smul_add, ← Matrix.smul_mul, hp u hu, hq u hu, Matrix.zero_mul, add_zero]

theorem udat_one {σ : E →ₐ[F] E} {d : ℕ} {J : Matrix (Fin d) (Fin d) E} {R : Type} [Zero R] {ev : AF F → R} :
    (1 : UD σ J) ∈ UDAt σ J ev := by
  intro u _
  simp

theorem det_ne_zero_of_hasSig {n r s : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} (h : HasSig M r s) : M.det ≠ 0 := by
  obtain ⟨hn, A, hA⟩ := h
  let e : Fin r ⊕ Fin s ≃ Fin n := finSumFinEquiv.trans (finCongr hn)
  have key : (A.submatrix id e.symm)ᵀ * M * (A.submatrix id e.symm).map star =
      (Aᵀ * M * A.map star).submatrix e.symm e.symm := by
    ext i j; rfl
  have hd := congrArg Matrix.det key
  rw [Matrix.det_submatrix_equiv_self, hA, Matrix.det_mul, Matrix.det_mul] at hd
  intro h0
  rw [h0] at hd
  simp [Matrix.det_fromBlocks_zero₂₁, Matrix.det_neg] at hd
  exact pow_ne_zero _ (by norm_num) hd.symm

theorem det_ne_zero_of_skew {σ : E →ₐ[F] E} {B : Base F E} {d r s : ℕ} {W : Spc F E d} (h : W.IsSkew σ B r s) :
    W.J.det ≠ 0 := by
  obtain ⟨φ⟩ : Nonempty (F →+* ℂ) := inferInstance
  have h0 := det_ne_zero_of_hasSig (h.sig (InfinitePlace.mk φ))
  intro e
  apply h0
  rw [Matrix.det_smul, show W.J.map _ = RingHom.mapMatrix _ W.J from rfl, ← RingHom.map_det, e, map_zero, mul_zero]

theorem mulLaw : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (ψ : AddChar (AF F) ℂ) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (v : Pl (F := F)) (t : E →ₐ[F] Fv F v)
    (b : GL (Fin n) (Fv F v)) (c : GL (Fin d) (Fv F v)) (dd : DblCo σ X W) (omd : DblRep σ (n := n) W),
    IsUSplitting (adeleClass F) ψ dd (actB (cA σ)) omd → LocOps omd v →
    ∀ ιd, IsLinD ψ dd t b c ιd → ∀ cd, IsShapeD omd t c ιd cd →
    cd 1 = 1 ∧ ∀ p ∈ UDAt σ W.J (evFin F v), ∀ q ∈ UDAt σ W.J (evFin F v), cd (p * q) = cd p * cd q := by
  intro F E _ _ _ _ _ σ ψ n d X W v t b c dd omd hS hL ιd hI cd hD
  obtain ⟨φ0, hφ0, hne⟩ : ∃ φ ∈ SB (Fin n × Fin d ⊕ Fin n × Fin d → Fv F v), ιd φ ≠ 0 := by
    have hmem : (intM (Fv F v) (Fin n) (Fin d ⊕ Fin d)).indicator (1 : Matrix (Fin n) (Fin d ⊕ Fin d) (Fv F v) → ℂ) ∈
        SB (Matrix (Fin n) (Fin d ⊕ Fin d) (Fv F v)) := indicator_intM_mem_SB
    obtain ⟨φ, hφ, he⟩ := hI.bij.surjOn hmem
    refine ⟨φ, hφ, fun h => ?_⟩
    have h0 := congrFun he 0
    rw [h, Set.indicator_of_mem (fun i j => by simp)] at h0
    simp at h0
  obtain ⟨Z, hZ⟩ : ∃ Z, ιd φ0 Z ≠ 0 := by
    by_contra h
    push_neg at h
    exact hne (funext h)
  have comp : ∀ p q : UD σ W.J, ∀ φ φ₁ φ₂ : (Fin n × Fin d ⊕ Fin n × Fin d → Fv F v) → ℂ,
      Acts (evFin F v) (omd q) φ φ₁ → Acts (evFin F v) (omd p) φ₁ φ₂ → Acts (evFin F v) (omd (p * q)) φ φ₂ := by
    intro p q φ φ₁ φ₂ hq hp r hr
    have h1 := hq r hr
    have hr1 : Rest (evFin F v) φ₁ r := ⟨hr.1, h1 ▸ hS.pres q _ hr.2⟩
    rw [map_mul, Module.End.mul_apply, h1, hp r hr1]
  refine ⟨?_, ?_⟩
  · have hA : Acts (evFin F v) (omd 1) φ0 φ0 := fun r _ => by rw [map_one, Module.End.one_apply]
    have e := congrFun (hD 1 udat_one φ0 hφ0 φ0 hφ0 hA) Z
    simp only [map_one, Units.val_one, Matrix.mul_one, Pi.smul_apply, smul_eq_mul] at e
    exact (mul_eq_right₀ hZ).mp e.symm
  · intro p hp q hq
    obtain ⟨φ₁, hφ₁, h1⟩ := hL q hq φ0 hφ0
    obtain ⟨φ₂, hφ₂, h2⟩ := hL p hp φ₁ hφ₁
    have e1 := hD q hq φ0 hφ0 φ₁ hφ₁ h1
    have e2 := hD p hp φ₁ hφ₁ φ₂ hφ₂ h2
    have e3 := hD (p * q) (udat_mul hp hq) φ0 hφ0 φ₂ hφ₂ (comp p q φ0 φ₁ φ₂ h1 h2)
    have hG : GlobalTheory.SplitFlip.invT (locMatD t c (p * q)) =
        GlobalTheory.SplitFlip.invT (locMatD t c p) * GlobalTheory.SplitFlip.invT (locMatD t c q) := by
      rw [map_mul, map_mul]
    set G := GlobalTheory.SplitFlip.invT (locMatD t c (p * q))
    have hY := congrFun (e3.symm.trans e2) (Z * (G⁻¹).val)
    rw [e1] at hY
    simp only [Pi.smul_apply, smul_eq_mul] at hY
    have k1 : Z * (G⁻¹).val * G.val = Z := by rw [Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.mul_one]
    have k2 : Z * (G⁻¹).val * (GlobalTheory.SplitFlip.invT (locMatD t c p)).val * (GlobalTheory.SplitFlip.invT (locMatD t c q)).val = Z := by
      rw [Matrix.mul_assoc, ← Units.val_mul, ← hG, k1]
    rw [k1, k2, ← mul_assoc] at hY
    exact mul_right_cancel₀ hZ hY

end GlobalTheory.DblScalDet


open GlobalTheory.DblScalDet in
theorem GlobalTheory.DblScal.scalar_factors_through_det : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ)
    (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (v : Pl (F := F)) (t : E →ₐ[F] Fv F v) (b : GL (Fin n) (Fv F v)) (c : GL (Fin d) (Fv F v))
      (dd : GlobalTheory.DblScal.DblCo σ X W) (omd : GlobalTheory.DblScal.DblRep σ (n := n) W),
      IsUSplitting (adeleClass F) B.ψ dd (actB (cA σ)) omd → GlobalTheory.DblScal.LocOps omd v →
      ∀ ιd, GlobalTheory.DblScal.IsLinD B.ψ dd t b c ιd → ∀ cd, GlobalTheory.DblScal.IsShapeD omd t c ιd cd →
      ∃ χd : (Fv F v)ˣ → ℂ, ∀ p ∈ GlobalTheory.DblScal.UDAt σ W.J (evFin F v),
        cd p = χd (GlobalTheory.SplitFlip.gdet (GlobalTheory.DblScal.locMatD t c p)) := by
  intro _ F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP v t b c dd omd hS hL ιd hI cd hD
  obtain ⟨h1, hmul⟩ := mulLaw F E σ B.ψ n d X W v t b c dd omd hS hL ιd hI cd hD
  have hJ : W.J.det ≠ 0 := det_ne_zero_of_skew hP.skew
  have hinj := GlobalTheory.T.local_matrix_map_injective F E σ hP.base.cm d W.J hJ v t c
  have hsurj := GlobalTheory.T.local_matrix_map_surjective F E σ hP.base.cm d W.J hJ hP.skew.skew v t c
  have hex : ∀ A : GL (Fin d ⊕ Fin d) (Fv F v), ∃ p ∈ GlobalTheory.DblScal.UDAt σ W.J (evFin F v), GlobalTheory.DblScal.locMatD t c p = A :=
    fun A => hsurj (Set.mem_univ A)
  choose sec hsU hs using hex
  have hsm : ∀ A A', sec (A * A') = sec A * sec A' := fun A A' =>
    hinj (hsU _) (udat_mul (hsU A) (hsU A')) (by rw [hs, map_mul, hs, hs])
  have hs1 : sec 1 = 1 := hinj (hsU 1) udat_one (by rw [hs, map_one])
  let f : GL (Fin d ⊕ Fin d) (Fv F v) →* ℂˣ :=
    { toFun := fun A => ⟨cd (sec A), cd (sec A⁻¹),
        by rw [← hmul _ (hsU _) _ (hsU _), ← hsm, mul_inv_cancel, hs1, h1],
        by rw [← hmul _ (hsU _) _ (hsU _), ← hsm, inv_mul_cancel, hs1, h1]⟩
      map_one' := Units.ext (by simp only [hs1, h1, Units.val_one])
      map_mul' := fun A A' => Units.ext (by simp only [Units.val_mul]; rw [hsm, hmul _ (hsU _) _ (hsU _)]) }
  let e : Fin d ⊕ Fin d ≃ Fin (d + d) := finSumFinEquiv
  let rr : GL (Fin (d + d)) (Fv F v) →* GL (Fin d ⊕ Fin d) (Fv F v) :=
    Units.map (Matrix.reindexAlgEquiv (Fv F v) (Fv F v) e.symm).toMonoidHom
  have h2 : (2 : Fv F v) ≠ 0 := fun h => two_ne_zero (α := F) ((algebraMap F (Fv F v)).injective (by rw [map_ofNat, h, map_zero]))
  obtain ⟨χ, hχ⟩ := GlobalTheory.ghom_factors_through_det (k := Fv F v) h2 (f.comp rr)
  refine ⟨fun x => (χ x : ℂ), fun p hp => ?_⟩
  have hp' : sec (GlobalTheory.DblScal.locMatD t c p) = p := hinj (hsU _) hp (hs _)
  set A := GlobalTheory.DblScal.locMatD t c p
  let A' : GL (Fin (d + d)) (Fv F v) := Units.map (Matrix.reindexAlgEquiv (Fv F v) (Fv F v) e).toMonoidHom A
  have hA : rr A' = A := Units.ext (by ext i j; simp [rr, A'])
  have hdet : Matrix.GeneralLinearGroup.det A' = GlobalTheory.SplitFlip.gdet A :=
    Units.ext (by simp [A', GlobalTheory.SplitFlip.gdet, Matrix.det_reindex_self])
  have hf := hχ A'
  rw [MonoidHom.comp_apply, hA, hdet] at hf
  calc cd p = cd (sec A) := by rw [hp']
    _ = ((f A : ℂˣ) : ℂ) := rfl
    _ = _ := by rw [hf]
end
end

section

noncomputable section

namespace GlobalTheory.ChrWSmooth

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem continuous_chrW {χ : Chr F E} (hχ : Continuous χ) {v : Pl F} (t : E →ₐ[F] Fv F v) :
    Continuous (chrW χ t) := by
  have hm : Continuous (Units.map (complMap (splitPrime_under t)).toMonoidHom) :=
    Units.continuous_map (GlobalTheory.LFun.SplitChart.continuous_complMap (splitPrime_under t))
  have h1 : Continuous fun x : (Fv F v)ˣ => ((chrW χ t x : ℂˣ) : ℂ) :=
    (continuous_locChar hχ (splitPrime t)).comp hm
  have h2 : Continuous fun x : (Fv F v)ˣ => (((chrW χ t x)⁻¹ : ℂˣ) : ℂ) := by
    have : (fun x : (Fv F v)ˣ => (((chrW χ t x)⁻¹ : ℂˣ) : ℂ)) = fun x => ((chrW χ t x⁻¹ : ℂˣ) : ℂ) := by
      funext x; rw [map_inv]
    rw [this]
    exact h1.comp continuous_inv
  exact Units.continuous_iff.2 ⟨h1, h2⟩

theorem isUnitaryChar_chrW (χ : Chr F E) {v : Pl F} (t : E →ₐ[F] Fv F v) :
    GlobalTheory.SmGL.IsUnitaryChar (chrW χ t) := fun g => by
  show ‖((Circle.toUnits _ : ℂˣ) : ℂ)‖ = 1
  exact Circle.norm_coe _

theorem chrW_nu_smooth_unitary : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ v, X.Good v →
    ∀ t : E →ₐ[F] Fv F v, GlobalTheory.SmGL.IsSmoothChar (chrW X.ν t) ∧ GlobalTheory.SmGL.IsUnitaryChar (chrW X.ν t) := by
  intro _ F E _ _ _ _ _ σ B a a' G X om om' hT v _ t
  have hν : Continuous X.ν := by
    show Continuous fun x => X.α x / X.β x
    exact hT.chars.heckeα.1.div' hT.chars.heckeβ.1
  exact ⟨GlobalTheory.RootEx.UniformLattices.isOpen_ker_of_continuous _ (continuous_chrW hν t), isUnitaryChar_chrW _ t⟩

end GlobalTheory.ChrWSmooth
end
end

section

open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped Classical

theorem _root_.GlobalTheory.T.witt_frame_darboux_coordinates : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W)
    (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' → ∀ (r₀ : ℕ) (Xf Yf : Matrix (Fin n) (Fin r₀) E),
    GlobalTheory.SiegelSet.IsWittFrame σ ((1 : E) • X.J.map σ) Xf Yf →
    ∃ (co : Darboux (symp (R := AF F) (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) X.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) W.J)) (Fin n × Fin d))
      (blk : Fin n × Fin d → Option (Fin r₀)),
      (∀ x : Matrix (Fin n) (Fin d) E, ∃ y z : Fin n × Fin d → F,
        co.e ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) ∧
      (∀ i : Fin r₀, (Finset.univ.filter (fun j => blk j = some i)).card = 2 * d) ∧
      ∀ t : Fin r₀ → ℝ, (∀ i, 0 < t i) → ∀ a, GlobalTheory.SiegelSet.IsTorusElt σ ((1 : E) • X.J.map σ) Xf Yf t a →
        ∀ a' : UA σ X.J, (a' : GL (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) = HA.mat (AF F) σ ((1 : E) • X.J.map σ) a →
        ∀ z : Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), co.e (mat a' * z) =
          (fun j => GlobalTheory.TorusTheta.infScale F (((blk j).elim 1 t)⁻¹) * (co.e z).1 j,
           fun j => GlobalTheory.TorusTheta.infScale F ((blk j).elim 1 t) * (co.e z).2 j) := by
  first | exact @GlobalTheory.TorusAdapted.adapted_torus | exact GlobalTheory.TorusAdapted.adapted_torus | (intros; apply GlobalTheory.TorusAdapted.adapted_torus <;> assumption)
end

section

open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped Classical

theorem _root_.GlobalTheory.T.theta_kernel_continuous_functional : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W)
    (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' → ∀ φ ∈ SB (Fin n × Fin d → Af F), ∀ (g : UA σ X.J) (h : UA σ W.J),
    ∃ T : SInf F (Fin n × Fin d) →L[ℂ] ℂ, ∀ f : SInf F (Fin n × Fin d), theta om (pureA F f φ) g h = T f := by
  first | exact @GlobalTheory.ThetaKernelCont.theta_pureA_clm | exact GlobalTheory.ThetaKernelCont.theta_pureA_clm | (intros; apply GlobalTheory.ThetaKernelCont.theta_pureA_clm <;> assumption)
end
