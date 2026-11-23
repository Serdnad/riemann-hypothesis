module

public import Development.WeilBound.ThetaLifts.SchwartzMoments.PolynomialFunctionalEvalContinuous
public import Development.WeilBound.ThetaLifts.TowerModels.PlaneMain
public import Development.WeilBound.ThetaLifts.SmallCones.ColsOfMul
public import Development.WeilBound.ThetaLifts.SmallCones.ThetaUniq
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle018
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle049
public import Development.WeilBound.ThetaLifts.SmallCones.KFinArch
import Formalism.LocalToGlobal.IndefiniteReal.Bundle014
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.AdeleLC
import GroundTheory.GlobalFields.TateThesis.Bundle006
public import Development.WeilBound.ThetaLifts.SmallCones.MatCancel
public import Development.WeilBound.ThetaLifts.SmallCones.WittOf
import Development.WeilBound.ThetaLifts.TowerModels.Bundle002
import Development.WeilBound.ThetaLifts.TowerModels.Bundle003
import Development.WeilBound.ThetaLifts.TowerModels.PlaneReal
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
import Mathlib.RingTheory.Finiteness.Lattice
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Baire.LocallyCompactRegular
import Mathlib.Topology.Compactness.Paracompact
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
public import Development.WeilBound.ThetaLifts.SmallCones.Bundle010

@[expose] public section

section

noncomputable section

namespace PositivityTheory.ThKCT.So

open NumberField IsDedekindDomain Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open PositivityTheory.ThKOwn.KPol
open scoped TensorProduct Classical Matrix

theorem sb_unif {Y : Type} [AddCommGroup Y] [TopologicalSpace Y] [IsTopologicalAddGroup Y] {g : Y → ℂ} (hg : g ∈ SB Y) :
    ∀ᶠ u in 𝓝 (0 : Y), ∀ y, g (y + u) = g y := by
  have h1 : ∀ᶠ u in 𝓝 (0 : Y), ∀ y ∈ tsupport g, g (y + u) = g y := by
    refine hg.2.isCompact.eventually_forall_of_forall_eventually fun y _ => ?_
    have a : Tendsto (fun z : Y × Y => z.2 + z.1) (𝓝 (0, y)) (𝓝 y) := by
      exact (continuous_snd.add continuous_fst).tendsto' ((0 : Y), y) y (add_zero y)
    filter_upwards [a.eventually (hg.1.eventually_eq y), (continuous_snd.tendsto ((0 : Y), y)).eventually (hg.1.eventually_eq y)]
      with z h h'
    rw [h, h']
  have h2 : ∀ᶠ u in 𝓝 (0 : Y), ∀ y ∈ tsupport g, g (y + -u) = g y := by
    have : Tendsto (fun u : Y => -u) (𝓝 0) (𝓝 0) := by simpa using continuous_neg.tendsto (0 : Y)
    exact this.eventually h1
  filter_upwards [h1, h2] with u a b y
  by_cases hy : y ∈ tsupport g
  · exact a y hy
  by_cases hy' : y + u ∈ tsupport g
  · rw [← b _ hy', add_neg_cancel_right]
  · rw [image_eq_zero_of_notMem_tsupport hy, image_eq_zero_of_notMem_tsupport hy']

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

def Lev (C U : Set (κ → Af F)) (Ψ : (κ → AF F) → ℂ) : Prop :=
  (∀ x, ∀ y ∉ C, Ψ (pt x y) = 0) ∧ ∀ x y, ∀ u ∈ U, Ψ (pt x (y + u)) = Ψ (pt x y)

theorem exists_lev {Ψ} (h : Ψ ∈ schA F κ) : ∃ C, IsCompact C ∧ ∃ U ∈ 𝓝 0, Lev C U Ψ := by
  induction h using Submodule.span_induction with
  | mem Φ h =>
    obtain ⟨f, g, hg, rfl⟩ := h
    exact ⟨_, hg.2.isCompact, _, sb_unif hg, fun x y hy => by rw [pureA_pt, image_eq_zero_of_notMem_tsupport hy, mul_zero],
      fun x y u hu => by rw [pureA_pt, pureA_pt, hu y]⟩
  | zero => exact ⟨∅, isCompact_empty, _, univ_mem, fun _ _ _ => rfl, fun _ _ _ _ => rfl⟩
  | add Φ Ψ _ _ h1 h2 =>
    obtain ⟨C, hC, U, hU, a, b⟩ := h1
    obtain ⟨C', hC', U', hU', a', b'⟩ := h2
    exact ⟨_, hC.union hC', _, inter_mem hU hU', fun x y hy => by
      rw [Pi.add_apply, a x y fun h => hy (Or.inl h), a' x y fun h => hy (Or.inr h), add_zero],
      fun x y u hu => by rw [Pi.add_apply, Pi.add_apply, b x y u hu.1, b' x y u hu.2]⟩
  | smul c Φ _ h =>
    obtain ⟨C, hC, U, hU, a, b⟩ := h
    exact ⟨C, hC, U, hU, fun x y hy => by rw [Pi.smul_apply, a x y hy, smul_zero],
      fun x y u hu => by rw [Pi.smul_apply, Pi.smul_apply, b x y u hu]⟩

def slc (P : Submodule ℂ (SInf F κ)) : Submodule ℂ ((κ → AF F) → ℂ) where
  carrier := {Ψ | ∀ y, ∃ f ∈ P, ∀ x, Ψ (pt x y) = f x}
  zero_mem' := fun _ => ⟨0, zero_mem _, fun _ => rfl⟩
  add_mem' := fun ha hb y => by
    obtain ⟨f, hf, e⟩ := ha y
    obtain ⟨f', hf', e'⟩ := hb y
    exact ⟨f + f', add_mem hf hf', fun x => by rw [Pi.add_apply, e, e', SchwartzMap.add_apply]⟩
  smul_mem' := fun c _ ha y => by
    obtain ⟨f, hf, e⟩ := ha y
    exact ⟨c • f, Submodule.smul_mem _ c hf, fun x => by rw [Pi.smul_apply, e, SchwartzMap.smul_apply]⟩

theorem slc_mono {P Q : Submodule ℂ (SInf F κ)} (h : P ≤ Q) : slc P ≤ slc Q := fun _ hΨ y =>
  (hΨ y).imp fun _ hf => ⟨h hf.1, hf.2⟩

def levS (C U : Set (κ → Af F)) : Submodule ℂ ((κ → AF F) → ℂ) where
  carrier := {Ψ | Lev C U Ψ}
  zero_mem' := ⟨fun _ _ _ => rfl, fun _ _ _ _ => rfl⟩
  add_mem' := fun ha hb => ⟨fun x y hy => by rw [Pi.add_apply, ha.1 x y hy, hb.1 x y hy, add_zero],
    fun x y u hu => by rw [Pi.add_apply, Pi.add_apply, ha.2 x y u hu, hb.2 x y u hu]⟩
  smul_mem' := fun c _ ha => ⟨fun x y hy => by rw [Pi.smul_apply, ha.1 x y hy, smul_zero],
    fun x y u hu => by rw [Pi.smul_apply, Pi.smul_apply, ha.2 x y u hu]⟩

theorem orbit_fin {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    (ρ : G →* Module.End ℂ ((κ → AF F) → ℂ)) (Φ : (κ → AF F) → ℂ) (hc : ∀ z, Continuous fun k => ρ k Φ z)
    (hs : ∀ k, ρ k Φ ∈ schA F κ) (P : Submodule ℂ (SInf F κ)) [FiniteDimensional ℂ P] (hP : ∀ k, ρ k Φ ∈ slc P) :
    FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k => ρ k Φ)) := by
  haveI : LocallyCompactSpace (Af F) := GlobalTheory.AdelicUnitaryTop.locallyCompact_finiteAdele F
  haveI : SecondCountableTopology (Af F) := GlobalTheory.AdelicUnitaryTop.secondCountable_finiteAdele F
  let C := CompactExhaustion.choice (κ → Af F)
  obtain ⟨U, hU⟩ := (𝓝 (0 : κ → Af F)).exists_antitone_basis
  obtain ⟨⟨a, b⟩, k₀, hk₀⟩ := nonempty_interior_of_iUnion_of_closed (f := fun p : ℕ × ℕ => {k | Lev (C p.1) (U p.2) (ρ k Φ)})
    (fun p => by
      simp only [Lev, Set.setOf_and, Set.setOf_forall]
      exact (isClosed_iInter fun x => isClosed_iInter fun y => isClosed_iInter fun _ => isClosed_eq (hc _) continuous_const).inter
        (isClosed_iInter fun x => isClosed_iInter fun y => isClosed_iInter fun u => isClosed_iInter fun _ => isClosed_eq (hc _) (hc _)))
    (Set.eq_univ_of_forall fun k => by
      obtain ⟨D, hD, V, hV, h1, h2⟩ := exists_lev (hs k)
      obtain ⟨a, ha⟩ := C.exists_superset_of_isCompact hD
      obtain ⟨b, hb⟩ := hU.mem_iff.1 hV
      exact Set.mem_iUnion.2 ⟨(a, b), fun x y hy => h1 x y fun h => hy (ha h), fun x y u hu => h2 x y u (hb hu)⟩)
  let Ω := slc P ⊓ levS (C a) (U b)
  let c : SInf F κ →ₗ[ℂ] ((κ → mixedEmbedding.mixedSpace F) → ℂ) :=
    { toFun := fun f => f, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  haveI : FiniteDimensional ℂ Ω := level_fin pt (fun z => ⟨_, _, pt_eta z⟩) c P (C.isCompact a) (hU.mem b) Ω (fun Ψ h => h.1)
    (fun Ψ h => h.2.1) fun Ψ h => h.2.2
  obtain ⟨s, -, hcov⟩ := isCompact_univ.elim_nhds_subcover
    (fun k₁ : G => (fun k => k₀ * k₁⁻¹ * k) ⁻¹' {k | Lev (C a) (U b) (ρ k Φ)}) fun k₁ _ =>
      (continuous_const.mul continuous_id).continuousAt.preimage_mem_nhds (by simpa using mem_interior_iff_mem_nhds.1 hk₀)
  refine Submodule.finiteDimensional_of_le (S₂ := ⨆ k₁ : s, Ω.map (ρ (k₁.1 * k₀⁻¹))) (Submodule.span_le.2 ?_)
  rintro _ ⟨k, rfl⟩
  obtain ⟨k₁, h₁, hk⟩ := Set.mem_iUnion₂.1 (hcov (Set.mem_univ k))
  refine Submodule.mem_iSup_of_mem ⟨k₁, h₁⟩ ⟨ρ (k₀ * k₁⁻¹ * k) Φ, ⟨hP _, hk⟩, ?_⟩
  rw [← Module.End.mul_apply, ← map_mul]
  congr 2
  group

end PositivityTheory.ThKCT.So

namespace PositivityTheory.ThKCT

open NumberField IsDedekindDomain Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open PositivityTheory.ThKOwn.KPol So
open scoped TensorProduct Classical Matrix

theorem kFinData_of (hS : StabEx) : KFinData := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP K hK Φ hΦ
  have hs := IsUWeilPair.isUSplitting hP.weil
  have h1 : Φ ∈ schA F (Fin n × Fin d) ∧ ∃ m, ∀ k ∈ K, om (k, 1) Φ ∈ slc (polM M B.emb m) := by
    induction hΦ using Submodule.span_induction with
    | mem Φ h =>
      obtain ⟨f, hf, φ, h1, h2, rfl⟩ := h
      obtain ⟨g, hg, e⟩ := GlobalTheory.CompanionTheory.Ar.RT.Inj.pure_eq_pureA M B.ψ hP.good φ h1 h2
      obtain ⟨m, hm⟩ := exists_polM M hP.base.std hf
      rw [e f]
      refine ⟨Submodule.subset_span ⟨f, g, hg, rfl⟩, m, fun k hk y => ?_⟩
      obtain ⟨A, hA⟩ := exists_slice hs.toIsSplitting (k, 1) hg y
      exact ⟨A f, polM_stab hP.base.std hs.toIsSplitting hg ((hK _).1 (inv_mem hk)).1 hA m hm, hA f⟩
    | zero => exact ⟨zero_mem _, 0, fun k _ => by rw [map_zero]; exact zero_mem _⟩
    | add a b _ _ ha hb =>
      obtain ⟨a1, m, hm⟩ := ha
      obtain ⟨b1, m', hm'⟩ := hb
      refine ⟨add_mem a1 b1, max m m', fun k hk => ?_⟩
      rw [map_add (f := _)]
      exact add_mem (slc_mono (fil_mono _ _ (le_max_left _ _)) (hm k hk)) (slc_mono (fil_mono _ _ (le_max_right _ _)) (hm' k hk))
    | smul c a _ ha =>
      obtain ⟨a1, m, hm⟩ := ha
      refine ⟨Submodule.smul_mem _ c a1, m, fun k hk => ?_⟩
      rw [map_smul]
      exact Submodule.smul_mem _ c (hm k hk)
  obtain ⟨h1, m, hm⟩ := h1
  refine ⟨h1, ?_⟩
  obtain ⟨K', -, -, hK', hc, -⟩ := hS F E σ B n X r s hP.base hP.herm
  obtain rfl : K = K' := Subgroup.ext fun g => (hK g).trans (hK' g).symm
  haveI : CompactSpace K := isCompact_iff_compactSpace.1 hc
  haveI := polM_fin M hP.base.cm B.emb m
  refine orbit_fin (om.comp ((MonoidHom.inl _ _).comp K.subtype)) Φ (fun z => ?_) (fun k => hs.pres _ _ h1) _ fun k => hm k.1 k.2
  let l : ((Fin n × Fin d → AF F) → ℂ) →ₗ[ℂ] ℂ := LinearMap.proj z
  have hl' : l ∈ (adeleClass F).adm (Fin n × Fin d) := fun g' _ =>
    ⟨g' (fun i => (z i).2) • (BoundedContinuousFunction.evalCLM ℂ (fun i => evI F (z i)) ∘L
      SchwartzMap.toBoundedContinuousFunctionCLM ℂ _ _), fun f => by simp [l, pureA, evI, mul_comm]⟩
  exact (hs.cont l hl' Φ h1).comp (continuous_subtype_val.prodMk continuous_const)

end PositivityTheory.ThKCT

end
end

section

noncomputable section

namespace PositivityTheory.ThKCT

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK Fr PositivityTheory.ThKG.Tow.Pln

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem cartan_low {n n₁ : ℕ} {M θ : Matrix (Fin n) (Fin n) ℂ} {θ₁ : Matrix (Fin n₁) (Fin n₁) ℂ}
    {ι : Matrix (Fin n) (Fin n₁) ℂ} {P : Matrix (Fin n₁) (Fin n) ℂ} (hP : P * ι = 1) (h : IsCartan M θ) (e : θ * ι = ι * θ₁) :
    IsCartan (ιᵀ * M * ι.map star) θ₁ := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨?_, ?_, fun x hx => ?_⟩
  · rw [← Matrix.one_mul (θ₁ * θ₁), ← hP, Matrix.mul_assoc, ← Matrix.mul_assoc ι, ← e, Matrix.mul_assoc θ, ← e,
      ← Matrix.mul_assoc θ, h1, Matrix.one_mul]
  · have m : ∀ {a b c : ℕ} (A : Matrix (Fin a) (Fin b) ℂ) (C : Matrix (Fin b) (Fin c) ℂ),
        (A * C).map star = A.map star * C.map star := fun A C => Matrix.map_mul (f := starRingEnd ℂ)
    calc _ = (ι * θ₁)ᵀ * M * (ι * θ₁).map star := by simp only [Matrix.transpose_mul, m, Matrix.mul_assoc]
      _ = ιᵀ * (θᵀ * M * θ.map star) * ι.map star := by rw [← e]; simp only [Matrix.transpose_mul, m, Matrix.mul_assoc]
      _ = _ := by rw [h2]
  · rw [← gram_vec, Matrix.mulVec_mulVec, ← e, ← Matrix.mulVec_mulVec]
    refine h3 _ fun h0 => hx ?_
    rw [← Matrix.one_mulVec x, ← hP, ← Matrix.mulVec_mulVec, h0, Matrix.mulVec_zero]

theorem splitLat_map {v : Pl F} (τ : E →ₐ[F] Fv F v) {n m : ℕ} {L : Submodule (𝓞 E) (Fin n → E)}
    {L' : Submodule (𝓞 E) (Fin m → E)} (A : Matrix (Fin m) (Fin n) E) (h : ∀ z ∈ L, A *ᵥ z ∈ L') {w : Fin n → Fv F v}
    (hw : w ∈ splitLat τ L) : A.map τ *ᵥ w ∈ splitLat τ L' :=
  splitLat_le τ ((splitLat τ L').comap ((A.map τ).mulVecLin.restrictScalars _)) (fun z hz => by
    have e : A.map τ *ᵥ (fun i => τ (z i)) = fun i => τ ((A *ᵥ z) i) :=
      funext fun i => (RingHom.map_mulVec (τ : E →+* Fv F v) A z i).symm
    show A.map τ *ᵥ (fun i => τ (z i)) ∈ splitLat τ L'
    rw [e]
    exact map_mem_splitLat τ (h z hz)) hw

theorem low_eps {B : Base F E} (hB : B.IsGood σ) {ε : E} {κ : ℂ} (hκ1 : κ * star κ = 1)
    (hκ : ∀ e : E →+* ℂ, star κ * e ε = κ) {D : Submodule (𝓞 E) E} {n n₁ : ℕ} {Y : Spc F E n} {Y₁ : Spc F E n₁}
    {H : Plane E n n₁} {i₀ i₁ r s : ℕ} (hY : IsEps σ B ε κ D Y r s) (hH : H.IsAdapted σ B Y Y₁ i₀ i₁) {ε' : E}
    {A' : Matrix (Fin n₁ ⊕ Fin 2) (Fin n) E} (h : IsFr (σ : E →+* E) ε' Y.J Y₁.J H.ι H.x H.y A') :
    1 ≤ r ∧ 1 ≤ s ∧ IsEps σ B ε κ D Y₁ (r - 1) (s - 1) := by
  have hcm := hB.cm
  set P : Matrix (Fin n₁) (Fin n) E := A'.submatrix Sum.inl id with hPd
  have hP : ∀ (u : Fin n₁ → E) (a b : E), P *ᵥ (H.ι *ᵥ u + a • H.x + b • H.y) = u := fun u a b => funext fun j => by
    have : A' *ᵥ (H.ι *ᵥ u + a • H.x + b • H.y) = Sum.elim u ![a, b] := by
      rw [← fr_mulVec, Matrix.mulVec_mulVec, h.inv2, Matrix.one_mulVec]
    exact congrFun this (Sum.inl j)
  have hPι : P * H.ι = 1 := Matrix.ext fun i j => by
    exact (congrFun (congrFun h.inv2 (Sum.inl i)) (Sum.inl j)).trans (by simp [Matrix.one_apply])
  have hform : ∀ u u', form σ Y₁.J u u' = form σ Y.J (H.ι *ᵥ u) (H.ι *ᵥ u') := hH.gram ▸ form_gram Y.J H.ι
  have hL : Y₁.L = Y.L.comap ((Matrix.mulVecLin H.ι).restrictScalars (𝓞 E)) := Submodule.ext hH.low
  have cg : ∀ e : E →+* ℂ, (H.ι.map e)ᵀ * (κ • Y.J.map e) * (H.ι.map e).map star = κ • Y₁.J.map e := fun e => by
    rw [Matrix.mul_smul, Matrix.smul_mul, map_gram hcm, hH.gram]
  have hPe : ∀ {S : Type} [CommRing S] (e : E →+* S), P.map e * H.ι.map e = 1 := fun e => by
    rw [← Matrix.map_mul, hPι, Matrix.map_one _ (map_zero _) (map_one _)]
  have hXX : ∀ e : E →+* ℂ, (fun i => e (H.x i)) ⬝ᵥ (κ • Y.J.map e) *ᵥ star (fun i => e (H.x i)) = 0 := fun e => by
    rw [Matrix.smul_mulVec, dotProduct_smul, ← map_form hcm, hH.xx, map_zero, smul_zero]
  have hmin : min r s ≠ 0 := fun h0 => by
    obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
    have h1 := aniso (hY.sig w) h0 (hXX _)
    have h2 : H.x = 0 := funext fun i => (B.emb w).1.injective ((congrFun h1 i).trans (map_zero _).symm)
    have e := hH.xy
    rw [h2, form, zero_dotProduct] at e
    exact zero_ne_one e
  have hlat : (Y.L.comap ((Matrix.mulVecLin H.ι).restrictScalars (𝓞 E))).IsLattice E :=
    Submodule.IsLattice.of_fg E (fg_comap _ (fun u u' e => by
      have := congrArg (P *ᵥ ·) (show H.ι *ᵥ u = H.ι *ᵥ u' from e)
      simpa [Matrix.mulVec_mulVec, hPι] using this) Y.L hY.lat.fg)
  have hfull : (Y.L.comap ((Matrix.mulVecLin H.ι).restrictScalars (𝓞 E))).IsFullLattice E := by
    let := hlat
    refine { span_eq_top := ?_ }
    apply top_unique
    intro u _
    have hz : H.ι *ᵥ u ∈ Submodule.span E (Y.L : Set (Fin n → E)) := by
      rw [Submodule.IsFullLattice.span_eq_top (self := hY.lat)]
      trivial
    have hmap : ∀ z ∈ Y.L, P *ᵥ z ∈
        Submodule.span E (Y.L.comap ((Matrix.mulVecLin H.ι).restrictScalars (𝓞 E)) : Set (Fin n₁ → E)) := by
      intro z hz
      obtain ⟨a, b, u', -, -, hu', rfl⟩ := hH.split z hz
      apply Submodule.subset_span
      change H.ι *ᵥ (P *ᵥ (a • H.x + H.ι *ᵥ u' + b • H.y)) ∈ Y.L
      rw [add_comm (a • H.x), hP]
      exact (hH.low u').1 hu'
    have hspan := (Submodule.span_le.mpr (show (Y.L : Set (Fin n → E)) ⊆
        (Submodule.span E (Y.L.comap ((Matrix.mulVecLin H.ι).restrictScalars (𝓞 E)) : Set (Fin n₁ → E))).comap (Matrix.mulVecLin P) from hmap)) hz
    simpa only [Submodule.mem_comap, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec,
      hPι, Matrix.one_mulVec] using hspan
  refine ⟨by omega, by omega, fun i j => ?_, fun w => ?_, hL ▸ hfull, fun u => ?_,
    fun w => ?_, fun v u => ?_⟩
  · rw [← form_single (σ := σ) Y₁.J j i, ← form_single (σ := σ) Y₁.J i j, hform, hform, form_swap hcm hY.herm]
  · rw [← cg]
    refine (real_plane _ (fun i => (B.emb w).1 (H.x i)) (κ • fun i => (B.emb w).1 (H.y i)) _ (P.map (B.emb w).1) hH.rank
      (map_herm hcm _ (hκ _) hY.herm) (hXX _) ?_ ?_ ?_ ?_ (hPe _) (hY.sig w)).1
    · rw [star_smul, Matrix.mulVec_smul, Matrix.smul_mulVec, smul_dotProduct, dotProduct_smul, dotProduct_smul,
        ← map_form hcm, hH.yy, map_zero, smul_zero, smul_zero, smul_zero]
    · rw [star_smul, Matrix.mulVec_smul, Matrix.smul_mulVec, dotProduct_smul, dotProduct_smul,
        ← map_form hcm, hH.xy, map_one, smul_eq_mul, smul_eq_mul, mul_one, mul_comm, hκ1]
    · rw [Matrix.smul_mulVec, Matrix.mulVec_smul, map_orth hcm _ Y.J H.ι H.x (fun u => (hH.orth u).1), smul_zero]
    · rw [star_smul, Matrix.mulVec_smul, Matrix.smul_mulVec, Matrix.mulVec_smul, Matrix.mulVec_smul,
        map_orth hcm _ Y.J H.ι H.y (fun u => (hH.orth u).2), smul_zero, smul_zero]
  · refine ⟨fun hu u' hu' => ?_, fun G => (hH.low u).2 ((hY.dual _).2 fun z hz => ?_)⟩
    · rw [hform]; exact (hY.dual _).1 ((hH.low u).1 hu) _ ((hH.low u').1 hu')
    · obtain ⟨_, _, u', -, -, hu', hz'⟩ := hH.split z hz
      rw [hz', form_add_right, form_add_right, form_smul_right, form_smul_right, (hH.orth u).1,
        (hH.orth u).2, mul_zero, mul_zero, zero_add, add_zero, ← hform]
      exact G u' hu'
  · rw [← cg]
    exact cartan_low (hPe _) (hY.cartan w) (hH.cartan w).1
  · have hn := hH.rank
    let f : Fin n₁ → Fin n := fun j => ⟨skip i₀ i₁ j, by have := j.2; unfold skip; split_ifs <;> omega⟩
    have hf : Function.Injective f := fun a b e => Fin.ext (by
      have := congrArg Fin.val e
      simp only [f, skip] at this
      split_ifs at this <;> omega)
    let T : Matrix (Fin n) (Fin n₁) (Fv F v.1) := (1 : Matrix (Fin n) (Fin n) _).submatrix id f
    have e1 : (Y.bas v).1 * T = H.ι.map (B.τ v) * (Y₁.bas v).1 := Matrix.ext fun a j => by
      rw [← (hH.bas v (f j)).2.2 j rfl a]
      simp [T, Matrix.mul_apply, Matrix.one_apply]
    have e2 : (∀ i, u i ∈ v.1.adicCompletionIntegers F) ↔ ∀ i, (T *ᵥ u) i ∈ v.1.adicCompletionIntegers F := by
      refine ⟨fun G i => sum_mem fun j _ => mul_mem ?_ (G j), fun G j => ?_⟩
      · simp only [T, Matrix.submatrix_apply, Matrix.one_apply]
        split_ifs
        exacts [one_mem _, zero_mem _]
      · simpa [T, Matrix.mulVec, dotProduct, Matrix.one_apply, hf.eq_iff] using G (f j)
    rw [e2, hY.bas v, Matrix.mulVec_mulVec, e1, ← Matrix.mulVec_mulVec]
    refine ⟨fun G => ?_, splitLat_map _ _ fun z hz => (hH.low z).1 hz⟩
    have := splitLat_map (L' := Y₁.L) _ P (fun z hz => by
      obtain ⟨a, b, u', -, -, hu', rfl⟩ := hH.split z hz
      rwa [add_comm (a • H.x), hP]) G
    rwa [Matrix.mulVec_mulVec, show P.map (B.τ v) * H.ι.map (B.τ v) = 1 from hPe (B.τ v : E →+* Fv F v.1),
      Matrix.one_mulVec] at this

theorem low_of : Low := by
  intro F E _ _ _ _ _ σ B n n₁ Y Y₁ H i₀ i₁ r s hB hH
  refine ⟨fun hY => ?_, fun hY => ?_⟩
  · obtain ⟨ε, A', h⟩ := isFr hB (Or.inl hY) hH
    simp only [isHerm_iff] at hY ⊢
    exact low_eps hB (by simp) (fun e => by simp) hY hH h
  · obtain ⟨ε, A', h⟩ := isFr hB (Or.inr hY) hH
    simp only [isSkew_iff] at hY ⊢
    exact low_eps hB (by simp) (fun e => by simp) hY hH h

end PositivityTheory.ThKCT

end
end
