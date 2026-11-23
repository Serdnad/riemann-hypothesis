module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle327
public import Formalism.SharpRestriction.LevelLetterCocycles.PairedCharacterCondition
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle251
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitOfClosure
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle243
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardLeOfSpan
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle338
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffZeroEqZeroIff
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle330
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsWeakTopologyWittTiltTensor
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormSubLtOneOfFix
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.RingTheory.PiTensorProduct
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
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle010
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle005
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle314
import Formalism.SharpRestriction.LevelLetterCocycles.DeltaInvariantLattices
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass Formalism.MainNotions.PairedCharacterCondition



noncomputable section

namespace GlobalTheory.Pass.LocCrysU

variable {D : D7} (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))

theorem loc_eq_map {k : ℕ} (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)) (g : Br.G D.nbr i w hw) :
    Br.loc D.nbr i w hw M g =
      (mapM (toK D.nd i) M ((Br.iota D.nbr i w hw g : Gw D.nd w) : GE D.nd)).map (Br.toLLK (D.nbr i w hw)) := by
  ext a b
  simp only [Br.loc, Br.locM, Br.locO, mapM, MonoidHom.coe_comp, Function.comp_apply, RingHom.toMonoidHom_eq_coe,
    MonoidHom.coe_coe, RingHom.mapMatrix_apply, Matrix.map_apply, toK]
  exact congrArg Subtype.val (Br.toLLK_alg (D.nbr i w hw) _).symm

theorem main : ∀ (D : D7), FontaineAtPlacesOverL (D := D) → ∀ (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))), GoodR D.nd i r → ∀ (Xs : Set (D.nd.X i)) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (n : ℕ), PotFam i w hw (fun x : ↥Xs => rTwO D.nd i r x) n → ∀ {k : ℕ} (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)), SubTw i r Xs M → ∀ (hM : Continuous fun g => M g), ∃ (K' : FinExt (D.nd.l i)) (h : (D.nbr i w hw).Kw.1 ≤ K'.1), IsCrys ((D.loc (D.nd.l i)).PD K') ((GlobalTheory.Pass.LocDirect.ModuleGaloisRepresentation i w hw M hM).ρ.comp (Subgroup.inclusion (GK_le h))) := by
  intro D hFo i r hr Xs w hw n hP k M hSub hM
  obtain ⟨K', h, hN, hFi, hS, Sig, Fr, -, -, -, -, hx⟩ := hP
  obtain ⟨-, x₀, hx₀, j, hjinj, hjeq⟩ := hSub
  refine ⟨K', h, ?_⟩
  haveI := GlobalTheory.Pass.LocDirect.isTopRing i w hw
  have hcont := (GlobalTheory.Pass.FamCont.stepCont D i r hr x₀).1
  have hc1 : Continuous (Br.loc D.nbr i w hw (rTwO D.nd i r x₀)) :=
    GlobalTheory.PotDual.continuous_loc D i w hw _ hcont
  have hinc : Continuous (Subgroup.inclusion (GK_le h)) :=
    Continuous.subtype_mk continuous_subtype_val _

  have hpc := (hx ⟨x₀, hx₀⟩).1
  have hcr := ((GlobalTheory.PcRes.main (D.nd.l i) (D.loc (D.nd.l i)) (D.nbr i w hw).Kw K' (D.nbr i w hw).LL h hN hFi hS
    _ (matRep (Br.loc D.nbr i w hw (rTwO D.nd i r x₀)))).2).1 hpc
  let A₁ := GlobalTheory.Pass.FinDesc.resG (Subgroup.inclusion (GK_le h)) hinc
    (GlobalTheory.PotDual.bundle ℚ_[D.nd.l i] (Br.OLL D.nbr i w hw) (Br.loc D.nbr i w hw (rTwO D.nd i r x₀)) hc1)
  let A₀ := GlobalTheory.Pass.FinDesc.resG (Subgroup.inclusion (GK_le h)) hinc (GlobalTheory.Pass.LocDirect.ModuleGaloisRepresentation i w hw M hM)

  let f := Br.toLLK (D.nbr i w hw)
  let J := (LinearMap.toMatrix' j).map f
  obtain ⟨jl, hjl⟩ := LinearMap.exists_leftInverse_of_injective j (LinearMap.ker_eq_bot.2 hjinj)
  have hJl : ((LinearMap.toMatrix' jl).map f) * J = 1 := by
    rw [← Matrix.map_mul, ← LinearMap.toMatrix'_comp, hjl, LinearMap.toMatrix'_id, Matrix.map_one _ (map_zero f) (map_one f)]
  let ι : A₀.V →ₗ[Br.LL D.nbr i w hw] A₁.V := Matrix.toLin' J
  have hinj : Function.Injective ι := by
    have e : ∀ z : Fin k → Br.LL D.nbr i w hw, ((LinearMap.toMatrix' jl).map f).mulVec (J.mulVec z) = z := fun z => by
      rw [Matrix.mulVec_mulVec, hJl, Matrix.one_mulVec]
    intro u v huv
    have huv' : J.mulVec u = J.mulVec v := huv
    rw [← e u, ← e v, huv']
  have hJeq : ∀ γ : GE D.nd, LinearMap.toMatrix' j * mapM (toK D.nd i) M γ =
      mapM (toK D.nd i) (rTwO D.nd i r x₀) γ * LinearMap.toMatrix' j := by
    intro γ
    apply Matrix.toLin'.injective
    apply LinearMap.ext
    intro v
    rw [Matrix.toLin'_mul, Matrix.toLin'_mul, LinearMap.comp_apply, LinearMap.comp_apply, Matrix.toLin'_toMatrix',
      Matrix.toLin'_apply, Matrix.toLin'_apply, hjeq]
  have h1 : ∀ g x, ι (A₀.ρ g x) = A₁.ρ g (ι x) := by
    intro g (x : Fin k → Br.LL D.nbr i w hw)
    have hmat : J * Br.loc D.nbr i w hw M (Subgroup.inclusion (GK_le h) g) =
        Br.loc D.nbr i w hw (rTwO D.nd i r x₀) (Subgroup.inclusion (GK_le h) g) * J := by
      rw [loc_eq_map, loc_eq_map, ← Matrix.map_mul, ← Matrix.map_mul, hJeq]
    have key : J.mulVec ((Br.loc D.nbr i w hw M (Subgroup.inclusion (GK_le h) g)).mulVec x) =
        (Br.loc D.nbr i w hw (rTwO D.nd i r x₀) (Subgroup.inclusion (GK_le h) g)).mulVec (J.mulVec x) := by
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hmat]
    exact key
  have hU : ∀ g, ∀ u ∈ LinearMap.range ι, A₁.ρ g u ∈ LinearMap.range ι := by
    rintro g _ ⟨x, rfl⟩
    exact ⟨A₀.ρ g x, h1 g x⟩
  let A₂ := A₁.quot (LinearMap.range ι) hU
  have hF := hFo (D.nd.l i) K' (D.nbr i w hw).LL
  exact ((hF.1 A₀ A₁ A₂ ι (LinearMap.range ι).mkQ h1 (fun _ _ => rfl) hinj (Submodule.mkQ_surjective _)
    (Submodule.ker_mkQ _).symm).1 hcr).1

end GlobalTheory.Pass.LocCrysU

end
end

section

open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models GlobalTheory.TopSteps GlobalTheory.Present GlobalTheory.RedFun Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped LaurentSeries PowerSeries TensorProduct

namespace GlobalTheory.RedFun

theorem exists_invariant_basis {F₀ F R M D : Type} [Field F₀] [Field F] [CommRing R] [AddCommGroup M] [Module R M]
    [Fintype D] (κ : F →+* R) (ι : F₀ →+* F) (σ : D → (F →+* F)) (t : D → (M →+ M)) (V : AddSubgroup M)
    (hV : ∀ c, ∀ y ∈ V, κ c • y ∈ V) {m : ℕ} (u : Fin m → M)
    (hu : ∀ y ∈ V, ∃ c : Fin m → F, y = ∑ j, κ (c j) • u j) (hσ : Function.Injective σ)
    (hsl : ∀ d c y, t d (κ c • y) = κ (σ d c) • t d y) (hst : ∀ d, ∀ y ∈ V, t d y ∈ V)
    (hav : ∀ d, ∀ y ∈ V, t d (∑ d', t d' y) = ∑ d', t d' y) (hid : ∃ d, ∀ y ∈ V, t d y = y)
    (hfix : ∀ c, (∀ d, σ d c = c) → ∃ c₀, ι c₀ = c) :
    ∃ s, s ≤ m ∧ ∃ w : Fin s → M, (∀ j, w j ∈ V) ∧ (∀ j d, t d (w j) = w j) ∧
      (∀ c : Fin s → F, ∑ j, κ (c j) • w j = 0 → c = 0) ∧
      (∀ y ∈ V, ∃ c : Fin s → F, y = ∑ j, κ (c j) • w j) ∧
      (∀ y ∈ V, (∀ d, t d y = y) → ∃ c : Fin s → F₀, y = ∑ j, κ (ι (c j)) • w j) := by
  classical
  let : Module F M := Module.compHom M κ
  have hs : ∀ (c : F) (y : M), c • y = κ c • y := fun _ _ => rfl
  let V' : Submodule F M := { V with smul_mem' := fun c y hy => hV c y hy }
  have h1 := GlobalTheory.stable_le_span_invariants_of_semilinear_family F M D σ t V' hσ (fun d c y _ => hsl d c y)
    hst hav hid
  obtain ⟨b, hb, hsp, hli⟩ := exists_linearIndependent F {y | y ∈ V' ∧ ∀ d, t d y = y}
  have hle : V' ≤ Submodule.span F (Set.range u) := by
    intro y hy
    obtain ⟨c, rfl⟩ := hu y hy
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ (c j) (Submodule.subset_span ⟨j, rfl⟩)
  have hbu : Set.range ((↑) : b → M) ≤ Submodule.span F (Set.range u) := by
    rintro _ ⟨x, rfl⟩
    exact hle (hb x.2).1
  have : Finite b := by
    have : Module.Finite F (Submodule.span F (Set.range u)) := Module.Finite.span_of_finite F (Set.finite_range u)
    have h0 : LinearIndependent F fun x : b => (⟨x.1, hbu ⟨x, rfl⟩⟩ : Submodule.span F (Set.range u)) :=
      LinearIndependent.of_comp (Submodule.subtype _) hli
    exact h0.finite
  have : Fintype b := Fintype.ofFinite b
  have hc := (linearIndependent_le_span_aux' _ hli (Set.range u) hbu).trans (Fintype.card_range_le u)
  rw [Fintype.card_fin] at hc
  let e := (Fintype.equivFin b).symm
  have hli' : LinearIndependent F (fun j => (e j : M)) := hli.comp e e.injective
  have hind : ∀ c : Fin (Fintype.card b) → F, ∑ j, κ (c j) • (e j : M) = 0 → c = 0 := fun c hc =>
    funext (Fintype.linearIndependent_iff.1 hli' c hc)
  have hgen : ∀ y ∈ V, ∃ c : Fin (Fintype.card b) → F, y = ∑ j, κ (c j) • (e j : M) := by
    intro y hy
    have h2 : y ∈ Submodule.span F (Set.range fun j => (e j : M)) := by
      have h3 : (Set.range fun j => (e j : M)) = b := by
        ext x
        constructor
        · rintro ⟨j, rfl⟩; exact (e j).2
        · intro hx; exact ⟨e.symm ⟨x, hx⟩, by simp⟩
      rw [h3, hsp]
      exact h1 hy
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun F).1 h2
    exact ⟨c, hc.symm⟩
  refine ⟨_, hc, fun j => e j, fun j => (hb (e j).2).1, fun j => (hb (e j).2).2, hind, hgen, ?_⟩
  intro y hy hinv
  obtain ⟨c, rfl⟩ := hgen y hy
  have h4 : ∀ j d, σ d (c j) = c j := by
    intro j d
    have h5 := hinv d

    rw [map_sum] at h5
    simp only [hsl, fun j => (hb (e j).2).2 d] at h5
    have h6 := hind (fun j => σ d (c j) - c j) (by
      simp only [map_sub, sub_smul, Finset.sum_sub_distrib, h5, sub_self])
    exact sub_eq_zero.1 (congrFun h6 j)
  choose c₀ hc₀ using fun j => hfix (c j) (h4 j)
  exact ⟨c₀, by simp only [hc₀]⟩

theorem exists_frame_of_invariants : ∀ {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K] [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K] {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B] [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR] [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR] {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ} (W : LocWach PD LL O v n) {RA RW : Type} [CommRing RA] [CommRing RW] [Algebra O RA] [Algebra O RW] {inclR : RA →ₐ[O] RW} {φR : RW →ₐ[O] RW} {gR : G → (RW →ₐ[O] RW)} {πA : RA} (E : EtTie W RA RW inclR φR gR πA) {k : Type} [Field k] [Algebra O k] {Rk : Type} [CommRing Rk] [Algebra k Rk] [Algebra O Rk] [IsScalarTower O k Rk] (ρ : RW →ₐ[O] Rk) (lam : O) (κ : k⸨X⸩ →+* Rk) (a : G → (Rk →ₐ[k] Rk)) (ι : k⸨X⸩ →+* k⸨X⸩) (σ : {δ // δ ∈ W.DelF} → (k⸨X⸩ →+* k⸨X⸩)), IsRed E ρ (k := k) lam κ → IsDel E ρ κ a ι σ → ∀ (T : LocLat G Qp LL O) (A : Ob k G) (q : ↥T.L.T →ₗ[O] (Fin A.m → k)), Onto T A q → ∀ i, (∃ u : Fin A.m → W.DD T, ∀ x, ∃ c : Fin A.m → k⸨X⸩, eps E ρ i • J E ρ T q x = ∑ j, κ (c j) • eps E ρ i • J E ρ T q (u j)) → ∃ β : Vc k A.m →+ Rk ⊗[k] (Fin A.m → k), IsFrame (κ.comp ι) (eps E ρ i) β ∧ ∀ y, (∃ x, β x = y) ↔ ∃ x : ↥(DΔ W T), y = eps E ρ i • J E ρ T q x := by
  intro G _ _ Qp K₀ K _ _ _ _ _ _ _ B BdR _ _ _ _ _ _ _ _ _ _ _ PD LL O _ _ _ _ _ v n W RA RW _ _ _ _ inclR φR gR πA
    E k _ _ Rk _ _ _ _ ρ lam κ a ι σ hR hD T A q hq i hu
  classical
  obtain ⟨u, hu⟩ := hu
  set ε := eps E ρ i with hε
  have hεε : ε * ε = ε := eps_idem E ρ i
  choose g hg using fun δ : {δ // δ ∈ W.DelF} => W.resΓ_onto δ.1
  let f : W.DD T →+ Rk ⊗[k] (Fin A.m → k) := (DistribSMul.toAddMonoidHom _ ε).comp (J E ρ T q)
  have hf : ∀ x, f x = ε • J E ρ T q x := fun _ => rfl
  let t : {δ // δ ∈ W.DelF} → (Rk ⊗[k] (Fin A.m → k) →+ Rk ⊗[k] (Fin A.m → k)) :=
    fun δ => (Act a A (g δ)).toAddMonoidHom
  have ht : ∀ δ x, t δ (f x) = f (W.γD T δ.1 x) := by
    intro δ x
    change Act a A (g δ) (ε • J E ρ T q x) = _
    rw [Act_smul, hD.a_eps, ← J_act E ρ hD.a_ρ T A q hq, hg, hf]
  have hsum : ∀ x, ∑ δ, t δ (f x) = f (∑ δ ∈ W.DelF, W.γD T δ x) := by
    intro x
    simp only [ht]

    rw [map_sum, Finset.sum_coe_sort W.DelF (fun δ => f (W.γD T δ x))]
  have hinv : ∀ x ∈ DΔ W T, ∀ δ, t δ (f x) = f x := by
    intro x hx δ
    rw [ht, hx δ.1 δ.2]
  have hV : ∀ c, ∀ y ∈ f.range, κ c • y ∈ f.range := by
    rintro c _ ⟨x, rfl⟩
    obtain ⟨e, he⟩ := hR.κ_of i c
    refine ⟨e • x, ?_⟩
    rw [hf, hf, J_smul, smul_smul, smul_smul, ← he, mul_comm]
  have hsl : ∀ d c y, t d (κ c • y) = κ (σ d c) • t d y := by
    intro d c y
    change Act a A (g d) (κ c • y) = κ (σ d c) • Act a A (g d) y
    rw [Act_smul, hD.a_κ _ d (hg d)]
  obtain ⟨s, hs, w, hwV, hwi, hind, hgen, hgen₀⟩ := exists_invariant_basis κ ι σ t f.range hV
    (fun j => f (u j)) (by rintro _ ⟨x, rfl⟩; exact hu x) hD.σ_inj hsl
    (by rintro d _ ⟨x, rfl⟩; exact ⟨_, (ht d x).symm⟩)
    (by rintro d _ ⟨x, rfl⟩; rw [hsum]; exact hinv _ (sum_mem_DΔ T x) d)
    ⟨⟨1, (W.DelF_def 1).2 ⟨1, one_pos, one_pow 1⟩⟩, by rintro _ ⟨x, rfl⟩; rw [ht, W.γD_one]⟩
    (fun c => (hD.σ_fix c).1)
  have hspan : ∀ y : Fin A.m → k, ε ⊗ₜ[k] y ∈ Submodule.span Rk (Set.range w) := by
    intro y
    obtain ⟨x, rfl⟩ := hq.1 y
    have key : ∀ z ∈ Submodule.span Rk (Set.range (J E ρ T q)), ε • z ∈ Submodule.span Rk (Set.range w) := by
      intro z hz
      induction hz using Submodule.span_induction with
      | mem z hz =>
        obtain ⟨x, rfl⟩ := hz
        obtain ⟨c, hc⟩ := hgen _ ⟨x, rfl⟩
        rw [← hf, hc]
        exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
      | zero => rw [smul_zero]; exact Submodule.zero_mem _
      | add y z _ _ hy hz => rw [smul_add]; exact Submodule.add_mem _ hy hz
      | smul r y _ hy => rw [smul_comm]; exact Submodule.smul_mem _ _ hy
    have := key _ (J_span E ρ T q x)
    rwa [TensorProduct.smul_tmul', smul_eq_mul, mul_one] at this
  have hm : A.m ≤ s := card_le_of_span (eps_idem E ρ i) (hR.eps_ne i) w (Pi.basisFun k (Fin A.m))
    (Pi.basisFun k (Fin A.m)).linearIndependent (fun j => hspan _)
  obtain rfl : s = A.m := le_antisymm hs hm
  let β : Vc k A.m →+ Rk ⊗[k] (Fin A.m → k) :=
    { toFun := fun c => ∑ j, κ (ι (c j)) • w j
      map_zero' := by simp
      map_add' := fun c c' => by simp [add_smul, Finset.sum_add_distrib] }
  have hβ : ∀ c, β c = ∑ j, κ (ι (c j)) • w j := fun _ => rfl
  have hβV : ∀ c, β c ∈ f.range := fun c => by
    rw [hβ]; exact AddSubgroup.sum_mem _ fun j _ => hV _ _ (hwV j)
  refine ⟨β, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [injective_iff_map_eq_zero]
    intro c hc
    have := hind (fun j => ι (c j)) hc
    funext j
    exact (map_eq_zero ι).1 (congrFun this j)
  · intro c x
    simp [hβ, Finset.smul_sum, smul_smul]
  · intro c
    obtain ⟨x, hx⟩ := hβV c
    rw [← hx, hf, smul_smul, hεε]
  · intro y
    refine Submodule.span_mono ?_ (hspan y)
    rintro _ ⟨j, rfl⟩
    refine ⟨Pi.single j 1, ?_⟩
    rw [hβ, Finset.sum_eq_single j]
    · simp
    · intro j' _ hj; simp [hj]
    · simp
  · intro y
    constructor
    · rintro ⟨c, rfl⟩
      obtain ⟨x, hx⟩ := hβV c
      have hi : ∀ δ, t δ (β c) = β c := by
        intro δ

        rw [hβ, map_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [hsl, hwi, (hD.σ_fix _).2 ⟨_, rfl⟩]
      obtain ⟨r, hr⟩ := hR.res_surj ((W.DelF.card : k)⁻¹)
      refine ⟨⟨r • ∑ δ ∈ W.DelF, W.γD T δ x, ?_⟩, ?_⟩
      · intro δ hδ
        rw [map_smul, sum_mem_DΔ T x δ hδ]
      · change _ = ε • J E ρ T q (r • _)
        rw [J_smulO, smul_comm, ← hf, ← hsum, hx, hr, algebraMap_smul]
        simp only [hi, Finset.sum_const, Finset.card_univ, Fintype.card_coe]
        rw [← Nat.cast_smul_eq_nsmul k, smul_smul, inv_mul_cancel₀ hD.card_ne, one_smul]
    · rintro ⟨x, rfl⟩
      obtain ⟨c, hc⟩ := hgen₀ _ ⟨x.1, rfl⟩ (hinv x.1 x.2)
      exact ⟨c, hc.symm⟩

end GlobalTheory.RedFun
end

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.Decompl
open scoped TensorProduct

theorem _root_.GlobalTheory.T.galoisFixedSubringTensorWitt_saturated_complete : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (LL : FinExt l) (H : Set (GQ l)), (∀ x, (l : RW LL) * x ∈ fixSub AI LL H → x ∈ fixSub AI LL H) ∧ (∀ x ∈ fixSub AI LL H, φRW LL x ∈ fixSub AI LL H) ∧ ∀ x : ℕ → RW LL, (∀ i, x i ∈ fixSub AI LL H) → ∃ y ∈ fixSub AI LL H, ∀ k : ℕ, ∃ r, y - ∑ i ∈ Finset.range k, (l : RW LL) ^ i * x i = (l : RW LL) ^ k * r := by
  first | exact @GlobalTheory.Decompl.FixL.fixSub_ladic | exact GlobalTheory.Decompl.FixL.fixSub_ladic | (intros; apply GlobalTheory.Decompl.FixL.fixSub_ladic <;> assumption)
end

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices GlobalTheory.WeakClosed
open scoped Topology PowerSeries.WithPiTopology



namespace GlobalTheory.WeakTop

theorem coords_one_tmul_smul {R O W T ι : Type} [CommRing R] [CommRing O] [Algebra R O] [CommRing W] [Algebra R W] [AddCommGroup T] [Module O T] [Module R T] [IsScalarTower R O T] [Fintype ι] [DecidableEq ι] (b : Module.Basis ι R T) (w : W) (z : (O ⊗[R] W) ⊗[O] T) (i : ι) :
    GlobalTheory.WeakTop.coords W O b (((1 : O) ⊗ₜ[R] w) • z) i = w * GlobalTheory.WeakTop.coords W O b z i := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [smul_add, map_add (f := _), Pi.add_apply, hx, hy, mul_add]
  | tmul r t =>
    induction r using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy =>
      simp only [add_tmul, smul_add, map_add (f := _), Pi.add_apply, hx, hy, mul_add]
    | tmul a w' =>
      rw [TensorProduct.smul_tmul', smul_eq_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul,
        coords_tmul, coords_tmul]
      simp only [Algebra.smul_def]
      ring

end GlobalTheory.WeakTop
end

section

namespace GlobalTheory.UnramifiedHilbertNinety

open GlobalTheory.UnramifiedCrys

theorem exists_mem_multilinear_ne_zero {R V ι : Type} [CommRing R] [AddCommGroup V] [Module R V]
    [Fintype ι] [DecidableEq ι] (f : (ι → V) →ₘₗ[R] R) (S : Set V)
    (hS : ∀ l : V →ₗ[R] R, (∀ s ∈ S, l s = 0) → l = 0) (v₀ : ι → V) (h₀ : f v₀ ≠ 0) :
    ∃ v : ι → V, (∀ i, v i ∈ S) ∧ f v ≠ 0 := by
  have key : ∀ T : Finset ι, ∃ v : ι → V, (∀ i ∈ T, v i ∈ S) ∧ f v ≠ 0 := by
    intro T
    induction T using Finset.induction_on with
    | empty => exact ⟨v₀, by simp, h₀⟩
    | insert a T ha ih =>
      obtain ⟨v, hv, hf⟩ := ih
      obtain ⟨s, hs, hne⟩ : ∃ s ∈ S, f (Function.update v a s) ≠ 0 := by
        by_contra hc
        push Not at hc
        have h1 := hS (f.toLinearMap v a) hc
        have h2 := LinearMap.congr_fun h1 (v a)
        rw [MultilinearMap.toLinearMap_apply, Function.update_eq_self] at h2
        exact hf h2
      refine ⟨Function.update v a s, fun i hi => ?_, hne⟩
      by_cases hia : i = a
      · subst hia
        rwa [Function.update_self]
      · rw [Function.update_of_ne hia]
        exact hv i ((Finset.mem_insert.1 hi).resolve_left hia)
  obtain ⟨v, hv, hf⟩ := key Finset.univ
  exact ⟨v, fun i => hv i (Finset.mem_univ i), hf⟩

theorem exists_matrix_coboundary (p : ℕ) [hp : Fact p.Prime] (G : Type) [Group G] (R : Type)
    [CommRing R] [IsDomain R] [CharP R p] (ρ : G →* (R ≃+* R)) (m : ℕ) (hm : 0 < m)
    (hfin : Finite (G ⧸ fixer ρ p m)) (r : ℕ) (M : G →* Matrix (Fin r) (Fin r) R)
    (hρ : ∀ g h i j, ρ g (M h i j) = M h i j) (hM : ∀ h i j, M h i j ^ p ^ m = M h i j)
    (hMN : ∀ g ∈ fixer ρ p m, M g = 1) :
    ∃ W : Matrix (Fin r) (Fin r) R, IsUnit W.det ∧ (∀ i j, W i j ^ p ^ m = W i j) ∧
      ∀ g, M g * W.map (ρ g) = W := by
  classical
  set N := fixer ρ p m with hN
  letI : Fintype (G ⧸ N) := Fintype.ofFinite _
  let χ : G ⧸ N → (fixedPow p R m →* R) := fun x =>
    (ρ x.out).toMonoidHom.comp (fixedPow p R m).subtype
  have hχ : Function.Injective χ := by
    intro x x' h
    rw [← x.out_eq, ← x'.out_eq]
    apply Quotient.sound
    apply QuotientGroup.leftRel_apply.2
    intro y hy
    have h1 : ρ x.out y = ρ x'.out y := DFunLike.congr_fun h ⟨y, hy⟩
    rw [map_mul, RingAut.mul_apply, ← h1, ← RingAut.mul_apply, ← map_mul, inv_mul_cancel, map_one,
      RingAut.one_apply]
  have hli := (linearIndependent_monoidHom (fixedPow p R m) R).comp χ hχ
  have hsum : ∀ (f : G → R), (∀ g, ∀ n ∈ N, f (g * n) = f g) → ∀ g,
      ∑ x : G ⧸ N, f (g * x.out) = ∑ x : G ⧸ N, f x.out := by
    intro f hf g
    refine Fintype.sum_equiv (MulAction.toPerm g) _ _ fun x => ?_
    obtain ⟨n, hn⟩ := QuotientGroup.mk_out_eq_mul N (g * x.out)
    have : MulAction.toPerm g x = QuotientGroup.mk (g * x.out) := by
      rw [MulAction.toPerm_apply]
      conv_lhs => rw [← x.out_eq]
      rfl
    rw [this, hn, hf _ _ n.2]
  let S : Set (Fin r → R) := {v | (∀ i, v i ^ p ^ m = v i) ∧
    ∀ g i, ∑ k, M g i k * ρ g (v k) = v i}
  have hb : ∀ (θ : fixedPow p R m) (j : Fin r),
      (fun i => ∑ x : G ⧸ N, ρ x.out θ * M x.out i j) ∈ S := by
    intro θ j
    have hθm : (θ : R) ^ p ^ m = θ := θ.2
    refine ⟨fun i => ?_, fun g i => ?_⟩
    · rw [sum_pow_char_pow]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [mul_pow, ← map_pow, hθm, hM]
    · have h2 := hsum (fun g => ρ g θ * M g i j) (fun g n hn => by
        simp only [map_mul, RingAut.mul_apply, hn θ hθm, hMN n hn, mul_one]) g

      simp only [map_sum, Finset.mul_sum]
      rw [← h2, Finset.sum_comm]
      refine Finset.sum_congr rfl fun x _ => ?_
      simp only [map_mul, RingAut.mul_apply, Matrix.mul_apply, hρ, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      ring
  have hS : ∀ l : (Fin r → R) →ₗ[R] R, (∀ s ∈ S, l s = 0) → l = 0 := by
    intro l hl
    refine LinearMap.pi_ext' fun j => LinearMap.ext_ring ?_
    have h1 := Fintype.linearIndependent_iff.1 hli (fun x => l (fun i => M x.out i j)) (by
      funext θ
      simp only [Finset.sum_apply, Function.comp, Pi.zero_apply, Pi.smul_apply, smul_eq_mul]
      have h3 : (fun i => ∑ x : G ⧸ N, ρ x.out θ * M x.out i j) =
          ∑ x : G ⧸ N, ρ x.out θ • (fun i => M x.out i j) := by
        funext i
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      have h4 := hl _ (hb θ j)

      rw [h3, map_sum] at h4
      rw [← h4]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [map_smul, smul_eq_mul, mul_comm]
      rfl) (QuotientGroup.mk 1)
    obtain ⟨n, hn⟩ := QuotientGroup.mk_out_eq_mul N (1 : G)
    simp only [hn, one_mul, hMN n n.2] at h1
    have h5 : (fun i => (1 : Matrix (Fin r) (Fin r) R) i j) = Pi.single j 1 := by
      funext i
      rw [Matrix.one_apply, Pi.single_apply]
    rw [h5] at h1
    simpa using h1
  obtain ⟨v, hv, hf⟩ := exists_mem_multilinear_ne_zero
    (Matrix.detRowAlternating (n := Fin r) (R := R)).toMultilinearMap S hS
    (1 : Matrix (Fin r) (Fin r) R) (by
      change (1 : Matrix (Fin r) (Fin r) R).det ≠ 0
      rw [Matrix.det_one]
      exact one_ne_zero)
  have hf' : ((Matrix.of v).transpose).det ≠ 0 := by
    rw [Matrix.det_transpose]
    exact hf
  have hW : ∀ i j, (Matrix.of v).transpose i j ^ p ^ m = (Matrix.of v).transpose i j :=
    fun i j => (hv j).1 i
  refine ⟨(Matrix.of v).transpose, ?_, hW, fun g => ?_⟩
  · set t := ((Matrix.of v).transpose).det with ht
    have htq : t ^ p ^ m = t := by
      rw [← iterateFrobenius_def, ht, RingHom.map_det]
      congr 1
      ext i j
      exact hW i j
    have h1 : 1 < p ^ m := Nat.one_lt_pow hm.ne' hp.out.one_lt
    have hu : t ^ (p ^ m - 2) * t = 1 := by
      apply mul_right_cancel₀ hf'
      rw [← pow_succ, ← pow_succ, one_mul, show p ^ m - 2 + 1 + 1 = p ^ m by omega, htq]
    exact IsUnit.of_mul_eq_one_right _ hu
  · ext i j
    exact (hv j).2 g i

end GlobalTheory.UnramifiedHilbertNinety
end
