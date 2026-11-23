module

public import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle010
public import Development.WeilBound.ThetaLifts.LatticeBasics.ContinuousFlat
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle010
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle015
import Development.WeilBound.ThetaLifts.LatticeBasics.FarRight
import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle001
public import Mathlib.Analysis.Matrix.MeasurableSpace
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AuxiliaryPrimeFunction
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle016
public import Development.WeilBound.ThetaLifts.FrameEstimates.Bundle003
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle008
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts

@[expose] public section

section



section
noncomputable section
namespace PositivityTheory.ThKEst
open scoped Matrix
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
namespace SignatureOfHermitianForm
end SignatureOfHermitianForm
theorem epsOf_of_k : _root_.PositivityTheory.ThKEst.EpsOf_k := by
  intro F E _ _ _ _ _ σ B hB n X r s hX
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  have hτ := hB.cm.2.2.2 (B.emb w).1
  rcases hX with hX | hX
  · have := SignatureOfHermitianForm.of_sig σ _ hτ X.J 1 one_ne_zero (r := r) (s := s) (by rw [one_smul]; exact hX.sig w)
    exact ⟨⟨Or.inl hX.herm, this.1⟩, this.2⟩
  · have := SignatureOfHermitianForm.of_sig σ _ hτ X.J Complex.I Complex.I_ne_zero (hX.sig w)
    exact ⟨⟨Or.inr hX.skew, this.1⟩, this.2⟩
end PositivityTheory.ThKEst
end
end
end

section



section
noncomputable section
namespace GlobalTheory.ThK.Dbl
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
def CptAll_k : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n : ℕ) (Y : Spc F E n) (r s : ℕ), _root_.UpperTheory.TP.W.GoodK σ B → (Y.IsHerm σ B r s ∨ Y.IsSkew σ B r s) → min r s = 0 → Cpt σ Y.J
theorem cptAll_of_k (h1 : PositivityTheory.ThKEst.GrpTop) (h2 : _root_.PositivityTheory.ThKEst.EpsOf_k) (h3 : PositivityTheory.ThKEst.SiegelAll) (h4 : PositivityTheory.ThKEst.FinVolU)
    (h5 : PositivityTheory.ThKF.Unimod) : _root_.GlobalTheory.ThK.Dbl.CptAll_k := by
  intro F E _ _ _ _ _ σ B n Y r s hB hY h0
  obtain ⟨e, -, hr⟩ := h2 F E σ B hB n Y r s hY
  obtain ⟨a1, a2, a3, a4, -, -, -, a5⟩ := h1 F E σ hB.cm n Y.J e
  obtain ⟨fr, g, -, ⟨Ω, hΩ, hc⟩, -⟩ := h3 F E σ hB.cm n Y.J e
  have r0 : fr.r = 0 := by have := hr fr g; omega
  have a0 : ∀ t, fr.a t = 1 := fun t => by
    have : t + t = t := funext fun i => absurd i.2 (by omega)
    have e := g.add t t
    rw [this] at e
    exact left_eq_mul.1 e
  have cov : ∀ x, ∃ γ ∈ ratU σ Y.J, γ * x ∈ Ω := fun x => by
    obtain ⟨γ, hγ, t, -, κ, hκ, e⟩ := hc x
    exact ⟨γ, hγ, by rwa [e, a0, one_mul]⟩
  obtain ⟨C, hC⟩ := a5 Ω hΩ
  obtain ⟨-, u1, u2⟩ : Countable (ratU σ Y.J) ∧ _ ∧ _ := e.1.elim
    (fun h => h5 F E σ hB.cm n Y.J 1 (fun i j => by simp [h]) e.2) fun h => h5 F E σ hB.cm n Y.J (-1) (fun i j => by simp [h]) e.2
  refine ⟨a1, a2, a3, a4, ⟨Ω, hΩ, cov⟩, ⟨C, fun x => ?_⟩, u1, h4 F E σ hB.cm n Y.J e, u2⟩
  obtain ⟨γ, hγ, hx⟩ := cov x
  exact (ciInf_le (OrderBot.bddBelow _) (⟨γ, hγ⟩ : ratU σ Y.J)).trans (hC _ hx)
section Gen
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G] {μ : Measure G}
  [μ.IsHaarMeasure] {Γ : Subgroup G} [Countable Γ] {D : Set G}
end Gen
variable {J : Matrix (Fin n) (Fin n) E}
end GlobalTheory.ThK.Dbl
end
end
end

section

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.ThK.Dbl
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.Doubling (absE)
def Stab2Cpt_k : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n : ℕ) (Y : Spc F E n) r s, _root_.UpperTheory.TP.W.GoodK σ B → (Y.IsHerm σ B r s ∨ Y.IsSkew σ B r s) →
    ∀ K, IsStab2 (σ := σ) (Y := Y) B K → IsCompact (K : Set (G2 σ Y))
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ} {Y : Spc F E n}
  {K : Subgroup (G2 σ Y)} {a : G2 σ Y → ℝ} {χ : Chr F E} {z s₀ : ℂ} {f : G2 σ Y → ℂ} {e : UA σ Y.J × UA σ Y.J →* G2 σ Y}
theorem kpair_cont_k {B : Base F E} {r s : ℕ} (hB : _root_.UpperTheory.TP.W.GoodK σ B) (hY : Y.IsHerm σ B r s ∨ Y.IsSkew σ B r s) (h0 : min r s = 0)
    (c : Cpt σ Y.J) (hχ : IsHecke F E χ) (he : ∀ h h', IsEmb h h' (e (h, h'))) (ce : Continuous e)
    (hK : IsCompact (K : Set (G2 σ Y))) (ha : IsHgt K a) (ca : Continuous a) (a0 : ∀ x, 0 < a x) (cf : Continuous f) (hf : Law χ z f)
    {U Ê} (hE : IsEisCont (flat a f s₀) U Ê) {μ : Measure (UA σ Y.J)} {D : Set (UA σ Y.J)} (hμ : μ.IsHaarMeasure)
    (hD : IsFundamentalDomain (ratU σ Y.J) D μ) {t₀ : ℝ} (hi : ∀ t, t₀ ≤ t → Integrable (fun g => a (e (1, g)) ^ t) μ) :
    (∀ φ, IsRapid φ → DifferentiableOn ℂ (fun s => kpair χ e μ D (Ê s) φ) U) ∧ ∃ t : ℝ, ∀ s : ℂ, t < s.re → s ∈ U ∧
      Integrable (fun g => flat a f s₀ s (e (1, g)) * detInv χ g) μ ∧ ∀ φ, IsRapid φ → kpair χ e μ D (Ê s) φ =
        ∫ g, flat a f s₀ s (e (1, g)) * detInv χ g * pet μ D (fun h => φ (h * g)) φ ∂μ := by
  have hJ := _root_.GlobalTheory.ThK.Dbl.aniso_of_k hB hY h0
  obtain ⟨t₁, half⟩ := hE.half
  haveI := c.sc; haveI := c.lc
  haveI := GlobalTheory.Doubling.isTopologicalRing_tens (F := F) (E := E) (R := AF F)
  haveI : IsFiniteMeasure (μ.restrict D) := ⟨by simpa using c.fin _ _ hμ hD⟩
  have bc : ∀ {φ : UA σ Y.J → ℂ}, IsRapid φ → An.BC φ := fun h => ⟨h.1, c.bdd h.1 h.2.1⟩
  have cE : ∀ s ∈ U, Continuous (Ê s) := fun s hs =>
    hE.cont.comp_continuous (f := fun x => (s, x)) (by fun_prop) fun _ => ⟨hs, trivial⟩
  have iv : ∀ s ∈ U, ∀ γ ∈ ratU σ Y.J, ∀ δ ∈ ratU σ Y.J, ∀ g g', Ê s (e (γ * g, δ * g')) = Ê s (e (g, g')) := fun s hs γ hγ δ hδ g g' =>
    An.ident hE.isOpen hE.conn (hE.hol _) (hE.hol _) (fun s hs => ⟨(half s hs).1, by
      rw [← Prod.mk_mul_mk, map_mul]; exact (hf.flat ha a0 s).eis_inv hχ hJ he (half s hs).2 hγ hδ _⟩) hs
  have ck : ∀ s ∈ U, An.BC fun y : UA σ Y.J × UA σ Y.J => Ê s (e y) * detInv χ y.2 := fun s hs =>
    An.BC.mul ⟨(cE s hs).comp ce, c.bdd₂ c ((cE s hs).comp ce) (iv s hs)⟩
      ⟨(continuous_detInv hχ).comp continuous_snd, 1, fun y => (norm_detInv _ _).le⟩
  have hol : ∀ {φ : UA σ Y.J → ℂ}, IsRapid φ → DifferentiableOn ℂ (fun s => kpair χ e μ D (Ê s) φ) U := fun {φ} h => by
    have b := ((bc h).comp (continuous_snd (X := UA σ Y.J))).mul ((bc h).comp continuous_fst).star
    refine An.diffOn_integral hE.isOpen (fun s hs => ((ck s hs).mul b).1.aestronglyMeasurable)
      (fun y => ((hE.hol _).mul_const _).mul_const _) fun S hS cS => ?_
    obtain ⟨Ω, hΩ, cov⟩ := c.cov
    obtain ⟨C, hC⟩ := (cS.prod ((hΩ.prod hΩ).image ce)).exists_bound_of_continuousOn
      (hE.cont.mono (Set.prod_mono hS (Set.subset_univ _)))
    obtain ⟨C', hC'⟩ := b.2
    refine ⟨C * C', fun s hs y => ?_⟩
    obtain ⟨γ, hγ, h1⟩ := cov y.1
    obtain ⟨δ, hδ, h2⟩ := cov y.2
    have := hC (s, e (γ * y.1, δ * y.2)) ⟨hs, _, ⟨h1, h2⟩, rfl⟩
    rw [iv s (hS hs) γ hγ δ hδ] at this
    rw [norm_mul, norm_mul, norm_detInv, mul_one]
    exact mul_le_mul this (hC' y) (norm_nonneg _) ((norm_nonneg _).trans this)
  refine ⟨fun _ => hol, max t₁ (t₀ + s₀.re - z.re), fun s hs => ?_⟩
  obtain ⟨u, sm⟩ := half s ((le_max_left _ _).trans_lt hs)
  have cs := continuous_flat (s₀ := s₀) cf ca a0 s
  obtain ⟨C, hC⟩ := (hf.flat (s₀ := s₀) ha a0 s).bound cs ha hK
  have i1 : Integrable (fun g => flat a f s₀ s (e (1, g))) μ :=
    ((hi (s - s₀ + z).re (by have := (le_max_right _ _).trans_lt hs; simp; linarith)).const_mul C).mono'
      (cs.comp (ce.comp (Continuous.prodMk_right 1))).aestronglyMeasurable (.of_forall fun g => hC _)
  have i2 := i1.mul_bdd (continuous_detInv hχ).aestronglyMeasurable (.of_forall fun g => (norm_detInv χ g).le)
  exact ⟨u, i2, fun φ h => An.far_right _ μ (ck s u) (bc h) i2
    (_root_.GlobalTheory.ThK.Dbl.unfold0_k F E σ B n Y r _ hB hY h0 χ e hχ he _ _ _ cs (cE s u) sm (hf.flat ha a0 s) μ D hμ hD i1 _ h)⟩
end GlobalTheory.ThK.Dbl
end
end
end

section



section
noncomputable section
open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)
namespace PositivityTheory.SiegelWeilFormula
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
structure Wk_k (B : Base F E) {m n : ℕ} (A : Spc F E m) (Y : Spc F E n) (r s : ℕ) (χ : Chr F E) (κ : Type) [Fintype κ]
    (dd : Darboux (symp (R := AF F) (cA σ) (-1) (incM F A.J) (dbl (incM F Y.J))) κ)
    (om : G2 σ Y →* Module.End ℂ ((κ → AF F) → ℂ)) (S : UA σ A.J →* Module.End ℂ ((κ → AF F) → ℂ))
    (l : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ) (b : GL (Fin n ⊕ Fin n) E) (K : Subgroup (G2 σ Y)) (a : G2 σ Y → ℝ)
    (μ : Measure (UA σ A.J)) (D : Set (UA σ A.J)) : Prop where
  good : _root_.UpperTheory.TP.W.GoodK σ B
  hm : 1 ≤ m
  hn : 1 ≤ n
  aniso : min r s = 0
  sign : A.IsHerm σ B r s ∧ (∀ i j, σ (Y.J j i) = -Y.J i j) ∨ A.IsSkew σ B r s ∧ ∀ i j, σ (Y.J j i) = Y.J i j
  hecke : IsHecke F E χ
  res : ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χ m
  dbl : IsDbl (σ := σ) (A := A) (Y := Y) B.ψ dd χ om S l
  frame : IsFrame2 σ Y b
  stdK : IsStdK (σ := σ) (Y := Y) B b K
  hgt : IsHgt K a
  haar : μ.IsHaarMeasure
  dom : IsFundamentalDomain (ratU σ A.J) D μ
structure SD_k (σ : E →ₐ[F] E) : Type 1 where
  B : Base F E
  m : ℕ
  n : ℕ
  A : Spc F E m
  Y : Spc F E n
  r : ℕ
  s : ℕ
  χ : Chr F E
  κ : Type
  [fin : Fintype κ]
  dd : Darboux (symp (R := AF F) (cA σ) (-1) (incM F A.J) (dbl (incM F Y.J))) κ
  om : G2 σ Y →* Module.End ℂ ((κ → AF F) → ℂ)
  S : UA σ A.J →* Module.End ℂ ((κ → AF F) → ℂ)
  l : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ
  b : GL (Fin n ⊕ Fin n) E
  K : Subgroup (G2 σ Y)
  a : G2 σ Y → ℝ
  μ : Measure (UA σ A.J)
  D : Set (UA σ A.J)
  bs : Module.Basis (Fin 2) F E
  ok : _root_.PositivityTheory.SiegelWeilFormula.Wk_k (σ := σ) B A Y r s χ κ dd om S l b K a μ D
attribute [instance] _root_.PositivityTheory.SiegelWeilFormula.SD_k.fin
namespace SD
variable (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ)
abbrev _root_.PositivityTheory.SiegelWeilFormula.SD_k.G : Type := G2 σ d.Y
abbrev _root_.PositivityTheory.SiegelWeilFormula.SD_k.Fn : Type := (d.κ → AF F) → ℂ
abbrev _root_.PositivityTheory.SiegelWeilFormula.SD_k.sch : Submodule ℂ d.Fn := schA F d.κ
def _root_.PositivityTheory.SiegelWeilFormula.SD_k.KFin (Φ : d.Fn) : Prop :=
  Φ ∈ d.sch ∧ FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : d.K => d.om k.1 Φ))
def _root_.PositivityTheory.SiegelWeilFormula.SD_k.T (Φ : d.Fn) (X : Mx F E d.m d.n) : ℂ := d.l (d.dd.rho d.B.ψ (X * (incM F d.b.1.toCols₂)ᵀ) Φ)
def _root_.PositivityTheory.SiegelWeilFormula.SD_k.gram (X Z : Mx F E d.m d.n) : Mx F E d.n d.n := Xᵀ * incM F d.A.J * Z.map (cA σ)
def _root_.PositivityTheory.SiegelWeilFormula.SD_k.tt (M : Mx F E d.n d.n) : AF F := Algebra.trace (AF F) (AE F E) M.trace
def _root_.PositivityTheory.SiegelWeilFormula.SD_k.cmb (c : Fin d.m × Fin d.n × Fin 2 → AF F) : Mx F E d.m d.n := fun i j => ∑ k, c (i, j, k) ⊗ₜ[F] d.bs k
def _root_.PositivityTheory.SiegelWeilFormula.SD_k.crd (X : Mx F E d.m d.n) (k : Fin d.m × Fin d.n × Fin 2) : AF F :=
  (Algebra.TensorProduct.basis (AF F) d.bs).repr (X k.1 k.2.1) k.2.2
def _root_.PositivityTheory.SiegelWeilFormula.SD_k.schM : Submodule ℂ (Mx F E d.m d.n → ℂ) := (schA F (Fin d.m × Fin d.n × Fin 2)).comap (LinearMap.funLeft ℂ ℂ d.cmb)
def _root_.PositivityTheory.SiegelWeilFormula.SD_k.ratM : AddSubgroup (Mx F E d.m d.n) := AddSubgroup.closure (Set.range fun X : Matrix (Fin d.m) (Fin d.n) E => incM F X)
def _root_.PositivityTheory.SiegelWeilFormula.SD_k.IsCov (ν : Measure (Mx F E d.m d.n)) : Prop :=
  ν.IsAddHaarMeasure ∧ ∃ 𝓕, IsAddFundamentalDomain d.ratM 𝓕 ν ∧ ν 𝓕 = 1
def _root_.PositivityTheory.SiegelWeilFormula.SD_k.IsW (ε : ℤˣ) (w : d.G) : Prop := inFrame d.b w = Matrix.fromBlocks 0 1 (((ε : ℤ) : AE F E) • 1) 0
def _root_.PositivityTheory.SiegelWeilFormula.SD_k.Ht (x : d.G) : ℝ≥0 := (d.a x).toNNReal
def _root_.PositivityTheory.SiegelWeilFormula.SD_k.eis (f : d.G → ℂ) (s₁ z : ℂ) : d.G → ℂ :=
  GlobalTheory.Eis.cosetSum (par2 σ d.Y) (rat2 σ d.Y) fun x => ((d.Ht x : ℝ) : ℂ) ^ (z - s₁) * f x
def _root_.PositivityTheory.SiegelWeilFormula.SD_k.Eis (f : d.G → ℂ) (s₁ : ℂ) : Prop := ∀ s₀ : ℂ,
  ∃ (U : Set ℂ) (p : Polynomial ℂ) (Ê : ℂ → d.G → ℂ) (t : ℝ), IsOpen U ∧ IsRightDomain U ∧ s₀ ∈ U ∧ p ≠ 0 ∧
    (∀ g, DifferentiableOn ℂ (Ê · g) U) ∧ ContinuousOn (fun y : ℂ × d.G => Ê y.1 y.2) (U ×ˢ Set.univ) ∧
    (∀ z ∈ U, ∀ γ ∈ rat2 σ d.Y, ∀ g, Ê z (γ * g) = Ê z g) ∧
    ∀ z : ℂ, t < z.re → (∀ C : Set d.G, IsCompact C → ∃ u : GlobalTheory.Eis.Cosets (par2 σ d.Y) (rat2 σ d.Y) → ℝ, Summable u ∧
        ∀ g ∈ C, ∀ q, ‖GlobalTheory.Eis.term (par2 σ d.Y) (rat2 σ d.Y) (fun x => ((d.Ht x : ℝ) : ℂ) ^ (z - s₁) * f x) g q‖ ≤ u q) ∧
      ∀ g, Ê z g = p.eval z * d.eis f s₁ z g
def _root_.PositivityTheory.SiegelWeilFormula.SD_k.Strong : Prop := ∃ r' s', d.Y.IsHerm σ d.B r' s' ∨ d.Y.IsSkew σ d.B r' s'
def _root_.PositivityTheory.SiegelWeilFormula.SD_k.sec0 (Φ : d.Fn) (x : d.G) : ℂ := d.l (d.om x Φ)
def _root_.PositivityTheory.SiegelWeilFormula.SD_k.EisAll : Prop := ∀ Φ, d.KFin Φ → d.Eis (d.sec0 Φ) (s0 d.m d.n)
abbrev _root_.PositivityTheory.SiegelWeilFormula.SD_k.I (Φ : d.Fn) : d.G → ℂ := thetaMean d.om d.S d.μ d.D Φ
def _root_.PositivityTheory.SiegelWeilFormula.SD_k.orb (T : nF σ d.Y d.b) (Φ : d.Fn) : ℂ :=
  ⨍ g in d.D, ∑' X : {X : Matrix (Fin d.m) (Fin d.n) E // d.gram (incM F X) (incM F X) = (-2 : ℤ) • T.1.1},
    d.T Φ (mat g⁻¹ * incM F X.1) ∂d.μ
def _root_.PositivityTheory.SiegelWeilFormula.SD_k.lamSet : Set ((d.G → ℂ) → ℂ) :=
  {L | ∃ nb lam 𝓖 T x, CoefData (σ := σ) (Y := d.Y) d.b nb lam 𝓖 ∧ IsND T ∧ L = fun f => fc d.B.ψ d.b nb lam 𝓖 f T x}
def _root_.PositivityTheory.SiegelWeilFormula.SD_k.cw (w : InfinitePlace F) {α β : Type} (X : Matrix α β (AE F E)) : Matrix α β ℂ := X.map (piInf (d.B.emb w))
end SD
structure RD_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) where
  ε : ℤˣ
  ζ : ℂ
  fr : InfinitePlace F → GL (Fin d.m) ℂ
  sg : InfinitePlace F → ℤˣ
  ι : InfinitePlace F → (GR d.n →* d.G)
  hε : d.b.1ᵀ * dbl d.Y.J * d.b.1.map σ = Matrix.fromBlocks 0 1 (((ε : ℤ) : E) • 1) 0
  hζ : ε = -1 ∧ ζ = 1 ∨ ε = 1 ∧ ζ = Complex.I
  hfr : ∀ w, ζ • ((fr w).1ᵀ * d.A.J.map (d.B.emb w).1 * (fr w).1.map star) = ((sg w : ℤ) : ℂ) • 1
  cont : ∀ w, Continuous (ι w)
  at_w : ∀ w y, dZ d.n ζ * d.cw w (inFrame d.b (ι w y)) = mR y * dZ d.n ζ
  off_w : ∀ w w' y, w' ≠ w → d.cw w' (inFrame d.b (ι w y)) = 1
  off_f : ∀ w y, finOne F • inFrame d.b (ι w y) = finOne F • (1 : Matrix _ _ (AE F E))
namespace RD
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d)
def _root_.PositivityTheory.SiegelWeilFormula.RD_k.loc (w : InfinitePlace F) (X : Mx F E d.m d.n) : Fin d.m → Fin d.n → ℂ := (((R.fr w)⁻¹).1 * d.cw w X).map star
def _root_.PositivityTheory.SiegelWeilFormula.RD_k.fockOn (s : Finset (InfinitePlace F)) : Submodule ℂ (Mx F E d.m d.n → ℂ) :=
  Submodule.span ℂ {f | ∃ (P : InfinitePlace F → PX d.m d.n) (g : (Fin d.m × Fin d.n × Fin 2 → Af F) → ℂ), g ∈ SB _ ∧
    f = fun X => (∏ w ∈ s, fP (P w) (R.loc w X)) * g fun k => (d.crd X k).2}
abbrev _root_.PositivityTheory.SiegelWeilFormula.RD_k.fock : Submodule ℂ (Mx F E d.m d.n → ℂ) := R.fockOn Finset.univ
abbrev _root_.PositivityTheory.SiegelWeilFormula.RD_k.away (w : InfinitePlace F) : Submodule ℂ (Mx F E d.m d.n → ℂ) := R.fockOn (Finset.univ.erase w)
def _root_.PositivityTheory.SiegelWeilFormula.RD_k.tens (w : InfinitePlace F) (f : (Fin d.m → Fin d.n → ℂ) → ℂ) (Ψ : Mx F E d.m d.n → ℂ) (X : Mx F E d.m d.n) : ℂ :=
  f (R.loc w X) * Ψ X
def _root_.PositivityTheory.SiegelWeilFormula.RD_k.IsLocOp (w : InfinitePlace F) (L : GR d.n → ((Fin d.m → Fin d.n → ℂ) → ℂ) → (Fin d.m → Fin d.n → ℂ) → ℂ) : Prop :=
  ∀ y f, IsSw f → IsSw (L y f) ∧ ∀ Ψ : Mx F E d.m d.n → ℂ,
    (∀ X Z, (∀ w', w' ≠ w → d.cw w' Z = 0) → finOne F • Z = 0 → Ψ (X + Z) = Ψ X) →
    ∀ Φ ∈ d.sch, d.T Φ = R.tens w f Ψ → d.T (d.om (R.ι w y) Φ) = R.tens w (L y f) Ψ
def _root_.PositivityTheory.SiegelWeilFormula.RD_k.IsLift (w : InfinitePlace F) (Ψ : Mx F E d.m d.n → ℂ) (φ : PX d.m d.n →ₗ[ℂ] d.Fn) : Prop :=
  ∀ P, φ P ∈ d.sch ∧ d.T (φ P) = R.tens w (fP P) Ψ
end RD
def TBij_k : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ),
  (∀ Φ ∈ d.sch, d.T Φ ∈ d.schM) ∧ (∀ f ∈ d.schM, ∃ Φ ∈ d.sch, d.T Φ = f) ∧ ∀ Φ ∈ d.sch, d.T Φ = 0 → Φ = 0
def TPar_k : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ), ∀ Φ ∈ d.sch,
  (∀ (x : d.G) (β : Mx F E d.n d.n), inFrame d.b x = Matrix.fromBlocks 1 β 0 1 →
    ∀ X, d.T (d.om x Φ) X = d.B.ψ (-(⅟(2 : AF F) * d.tt (β * d.gram X X))) * d.T Φ X) ∧
  (∀ (x : d.G) (t u : GL (Fin d.n) (AE F E)), inFrame d.b x = Matrix.fromBlocks t.1 0 0 u.1 →
    ∀ X, d.T (d.om x Φ) X = (d.χ (Matrix.GeneralLinearGroup.det t) : ℂ) *
      (((absE F E (Matrix.GeneralLinearGroup.det t) : ℝ) ^ ((d.m : ℝ) / 2) : ℝ) : ℂ) * d.T Φ (X * (u⁻¹).1ᵀ)) ∧
  ∀ g X, d.T (d.S g Φ) X = d.T Φ (mat g⁻¹ * X)
def TWeyl_k : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ), ∀ ν, d.IsCov ν → ∀ ε w, d.IsW ε w → ∀ Φ ∈ d.sch,
  ∀ X, d.T (d.om w Φ) X = ∫ Z, d.B.ψ (((ε : ℤ) : AF F) * d.tt (d.gram X Z)) * d.T Φ Z ∂ν
def TTheta_k : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ), ∀ Φ ∈ d.sch,
  HasSum (fun X : Matrix (Fin d.m) (Fin d.n) E => d.T Φ (incM F X)) (thetaSum F Φ) ∧
  ∀ x g, d.om x (d.S g Φ) = d.S g (d.om x Φ)
def ThetaAuto_k : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ), d.μ d.D ≠ 0 ∧ d.μ d.D ≠ ⊤ ∧ ∀ Φ ∈ d.sch,
  (∀ x, IntegrableOn (fun g => thetaSum F (d.om x (d.S g Φ))) d.D d.μ) ∧ Continuous (d.I Φ) ∧
  ∀ γ ∈ rat2 σ d.Y, ∀ x, d.I Φ (γ * x) = d.I Φ x
def ThetaCoef_k : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ), ∀ Φ ∈ d.sch,
  ∀ nb lam 𝓖, CoefData (σ := σ) (Y := d.Y) d.b nb lam 𝓖 → ∀ T x, fc d.B.ψ d.b nb lam 𝓖 (d.I Φ) T x = d.orb T (d.om x Φ)
def TAll_k : Prop := _root_.PositivityTheory.SiegelWeilFormula.TBij_k ∧ _root_.PositivityTheory.SiegelWeilFormula.TPar_k ∧ _root_.PositivityTheory.SiegelWeilFormula.TWeyl_k ∧ _root_.PositivityTheory.SiegelWeilFormula.TTheta_k ∧ _root_.PositivityTheory.SiegelWeilFormula.ThetaAuto_k
def CoefEx_k : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ), ∃ nb lam 𝓖, CoefData (σ := σ) (Y := d.Y) d.b nb lam 𝓖
def RDEx_k : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ), Nonempty (_root_.PositivityTheory.SiegelWeilFormula.RD_k d)
def SiegelWeilDatumProperties : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ), (∃ ν, d.IsCov ν) ∧ (∃ ε w, d.IsW ε w ∧ w ∈ rat2 σ d.Y) ∧
  IsTopologicalGroup d.G ∧ LocallyCompactSpace d.G ∧ T2Space d.G ∧ SecondCountableTopology d.G
def FockMem_k : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d), R.fock ≤ d.schM ∧
  (∀ w, ∀ Ψ ∈ R.away w, (∀ P, R.tens w (fP P) Ψ ∈ R.fock) ∧
    ∀ X Z, (∀ w', w' ≠ w → d.cw w' Z = 0) → finOne F • Z = 0 → Ψ (X + Z) = Ψ X) ∧
  ∀ w, ∀ f ∈ R.fock, ∃ (k : ℕ) (P : Fin k → PX d.m d.n) (Ψ : Fin k → Mx F E d.m d.n → ℂ),
    (∀ i, Ψ i ∈ R.away w) ∧ f = ∑ i, R.tens w (fP (P i)) (Ψ i)
def LiftEx_k : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d), ∀ w, ∀ Ψ ∈ R.away w, ∃ φ, R.IsLift w Ψ φ
def LocOpEx_k : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d), ∀ w, ∃ L, R.IsLocOp w L
def LocInst_k : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d), ∀ w L, R.IsLocOp w L →
  ∃ (sL : PX d.m d.n →ₗ[ℂ] (GR d.n → ℂ)) (ρ : GR d.n → PX d.m d.n →ₗ[ℂ] PX d.m d.n) (p q : ℕ) (e : ℤ),
    (d.n ≤ d.m → GoodSig d.n p q) ∧ LocData (fun _ => true) (2 * Real.pi) (2 * Real.pi * ((R.sg w : ℤ) : ℝ)) p q e sL ρ ∧
    (∀ P y, sL P y = L y (fP P) 0) ∧ ∀ (k : GR d.n) P, InK (mR k) → L k (fP P) = fP (ρ k P)
def GSplit_k : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d), ∀ w L, R.IsLocOp w L → ∀ Ψ ∈ R.away w, ∀ φ, R.IsLift w Ψ φ →
  ∀ g : d.G, ∃ (x : d.G) (y : GR d.n) (c : ℂ) (r : ℝ), 0 < r ∧ g = x * R.ι w y ∧
    ∀ y' : GR d.n, (d.Ht (x * R.ι w y') : ℝ) = r * hLoc y' ∧ ∀ P, d.sec0 (φ P) (x * R.ι w y') = c * L y' (fP P) 0
def GIinv_k : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d), ∀ w, ∀ Ψ ∈ R.away w, ∀ φ, R.IsLift w Ψ φ →
  ∀ g a b P, d.I (φ (hOp (fun _ => true) (2 * Real.pi) a b P)) g = 0
def GIdil_k : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d), ∀ w, ∀ Ψ ∈ R.away w, ∀ φ, R.IsLift w Ψ φ →
  ∀ (g : d.G) (X : Fin d.n → ℝ) (a : ℝ → GR d.n), (∀ t, IsDil X t (a t)) → ∃ (U : Set ℂ) (H : GR d.n → ℂ → ℂ), IsOpen U ∧
    (∀ t : ℝ, (t : ℂ) ∈ U) ∧ ContinuousOn (fun y : GR d.n × ℂ => H y.1 y.2) (Set.univ ×ˢ U) ∧ ∀ y, DifferentiableOn ℂ (H y) U ∧
      (∀ t : ℝ, H y t = d.I (φ 1) (g * R.ι w (y * a t))) ∧
      ∀ r : ℕ, iteratedDeriv r (H y) 0 = d.I (φ ((dil (2 * Real.pi) X ^ r) 1)) (g * R.ι w y)
def KFinPoly_k : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d), ∀ Φ, d.KFin Φ → d.T Φ ∈ R.fock
def PolyKFin_k : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d), ∀ Φ ∈ d.sch, d.T Φ ∈ R.fock → d.KFin Φ
def SecK_k : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ), ∀ Φ, d.KFin Φ → IsSec d.K d.χ (s0 d.m d.n) (d.sec0 Φ)
def EisStrong_k : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ), d.Strong → ∀ s₁ f, IsSec d.K d.χ s₁ f → d.Eis f s₁
def LamBd_k : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ), ∀ L ∈ d.lamSet,
  (∀ (a : ℂ) (f f' : d.G → ℂ), Continuous f → Continuous f' → (∀ γ ∈ rat2 σ d.Y, ∀ g, f (γ * g) = f g) →
    (∀ γ ∈ rat2 σ d.Y, ∀ g, f' (γ * g) = f' g) → L (a • f + f') = a * L f + L f') ∧
  ∃ C : Set d.G, IsCompact C ∧ ∀ (f : d.G → ℂ) (M : ℝ), Continuous f → (∀ γ ∈ rat2 σ d.Y, ∀ g, f (γ * g) = f g) →
    (∀ x ∈ C, ‖f x‖ ≤ M) → ‖L f‖ ≤ M
def FourierZero_k : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ), ∀ nb lam 𝓖, CoefData (σ := σ) (Y := d.Y) d.b nb lam 𝓖 → ∀ f : d.G → ℂ, Continuous f →
  (∀ β ∈ nF σ d.Y d.b, ∀ g, f (nb β * g) = f g) → (∀ T g, fc d.B.ψ d.b nb lam 𝓖 f T g = 0) → f = 0
def DenseW_k : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d), ∀ w (y : GR d.n) (O : Set (GR d.n)), IsOpen O → y ∈ O →
  ∃ γ ∈ rat2 σ d.Y, ∃ y' ∈ O, ∃ x : d.G, γ = x * R.ι w y' ∧ ∀ y'' : GR d.n, x * R.ι w y'' = R.ι w y'' * x
def LamSing_k : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d), ∀ w (f : d.G → ℂ), Continuous f → (∀ γ ∈ rat2 σ d.Y, ∀ g, f (γ * g) = f g) →
  (∀ L ∈ d.lamSet, L f = 0) → ∀ ψ₀, IsSingTest ψ₀ → ∀ nb : (Fin d.n → Fin d.n → ℝ) → GR d.n, (∀ x, mR (nb x) = nU (herm x)) →
    ∀ (g : d.G) (a b : GR d.n), ∫ x, f (g * R.ι w (a * nb x * b)) * ψ₀ x = 0
def Unfold_k : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ), ∀ s₁ f, IsSec d.K d.χ s₁ f → d.Eis f s₁ → ∃ t : ℝ, ∀ z : ℂ, t < z.re →
  ∀ nb lam 𝓖, CoefData (σ := σ) (Y := d.Y) d.b nb lam 𝓖 → ∀ ε w, d.IsW ε w → ∀ x,
    Integrable (fun β => flat d.a f s₁ z (w * nb β * x)) lam ∧ ∀ T, IsND T →
      fc d.B.ψ d.b nb lam 𝓖 (d.eis f s₁ z) T x = ∫ β, flat d.a f s₁ z (w * nb β * x) * d.B.ψ (-d.tt (T.1.1 * β.1)) ∂lam
def WhitK_k : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ), d.n < d.m → d.EisAll → ∀ Φ, d.KFin Φ →
  ∀ nb lam 𝓖, CoefData (σ := σ) (Y := d.Y) d.b nb lam 𝓖 → ∀ ε w, d.IsW ε w → ∀ T, IsND T → ∀ x,
    HolValueAt (fun z => ∫ β, flat d.a (d.sec0 Φ) (s0 d.m d.n) z (w * nb β * x) * d.B.ψ (-d.tt (T.1.1 * β.1)) ∂lam)
      (s0 d.m d.n) (d.orb T (d.om x Φ))
def Main_k : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ), d.n < d.m → d.EisAll → ∀ Φ, d.KFin Φ → ∀ x,
  HolValueAt (fun z => d.eis (d.sec0 Φ) (s0 d.m d.n) z x) (s0 d.m d.n) (d.I Φ x)
def MainOf_k : Prop :=
  AbsThm → _root_.PositivityTheory.SiegelWeilFormula.TAll_k → _root_.PositivityTheory.SiegelWeilFormula.ThetaCoef_k → _root_.PositivityTheory.SiegelWeilFormula.RDEx_k → _root_.PositivityTheory.SiegelWeilFormula.SiegelWeilDatumProperties → _root_.PositivityTheory.SiegelWeilFormula.FockMem_k → _root_.PositivityTheory.SiegelWeilFormula.LiftEx_k → _root_.PositivityTheory.SiegelWeilFormula.LocOpEx_k → _root_.PositivityTheory.SiegelWeilFormula.LocInst_k → _root_.PositivityTheory.SiegelWeilFormula.GSplit_k → _root_.PositivityTheory.SiegelWeilFormula.GIinv_k → _root_.PositivityTheory.SiegelWeilFormula.GIdil_k → _root_.PositivityTheory.SiegelWeilFormula.KFinPoly_k →
    _root_.PositivityTheory.SiegelWeilFormula.PolyKFin_k → _root_.PositivityTheory.SiegelWeilFormula.SecK_k → _root_.PositivityTheory.SiegelWeilFormula.LamBd_k → _root_.PositivityTheory.SiegelWeilFormula.LamSing_k → _root_.PositivityTheory.SiegelWeilFormula.Unfold_k → _root_.PositivityTheory.SiegelWeilFormula.WhitK_k → _root_.PositivityTheory.SiegelWeilFormula.Main_k
def HeadOf_k : Prop := _root_.GlobalTheory.ThK.Dbl.EisBL_k → _root_.PositivityTheory.SiegelWeilFormula.SecK_k → _root_.PositivityTheory.SiegelWeilFormula.EisStrong_k → _root_.PositivityTheory.SiegelWeilFormula.Main_k → _root_.PositivityTheory.SiegelWeilFormula.SWStdLt_k
end PositivityTheory.SiegelWeilFormula
end
end
end
