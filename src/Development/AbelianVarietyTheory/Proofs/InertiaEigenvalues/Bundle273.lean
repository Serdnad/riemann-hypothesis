module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle127
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle073
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle084
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle222
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle258
public import Formalism.SharpRestriction.LevelLetterCocycles.RamificationTwoAndConjugationAtQAndD
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnipotentBlockColumnIndex
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle249
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle248
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
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.IntegralCasts.Bundle001

@[expose] public section

section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.JacStages GlobalTheory.InertSupp

namespace GlobalTheory.JacStagesExact

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {s : ℕ} {d : Fin s → ℕ} {t : Fin s → ℕ} {d' : ∀ a, Fin (t a) → ℕ}
  {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

def relJacMap (e' : ∀ a, (Σ b, Fin (d' a b)) ≃ Fin (d a))
    {σ : Representation ℂ (Levi k fun a => Fin (d a)) V}
    {τ : Representation ℂ (Levi k fun a => Fin (d a)) W} (f : σ.IntertwiningMap τ) :
    (relJacD e' σ).IntertwiningMap (relJacD e' τ) :=
  twistMap (jacquetMap f _ _ _) _

theorem relJacMap_surjective (e' : ∀ a, (Σ b, Fin (d' a b)) ≃ Fin (d a))
    {σ : Representation ℂ (Levi k fun a => Fin (d a)) V}
    {τ : Representation ℂ (Levi k fun a => Fin (d a)) W} (f : σ.IntertwiningMap τ)
    (hf : Function.Surjective f) : Function.Surjective (relJacMap e' f) := fun y => by
  obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  obtain ⟨v, rfl⟩ := hf w
  exact ⟨Submodule.Quotient.mk v, rfl⟩

theorem relJacMap_injective (e' : ∀ a, (Σ b, Fin (d' a b)) ≃ Fin (d a))
    {σ : Representation ℂ (Levi k fun a => Fin (d a)) V}
    {τ : Representation ℂ (Levi k fun a => Fin (d a)) W} (hτ : IsSmooth τ) (f : σ.IntertwiningMap τ)
    (hf : Function.Injective f) : Function.Injective (relJacMap e' f) := by
  classical
  refine (injective_iff_map_eq_zero _).2 fun x hx => ?_
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  have h1 : f v ∈ twKer τ (relUnipD k e') 1 := (Submodule.Quotient.mk_eq_zero _).1 hx
  obtain ⟨S, hS, h2⟩ := GlobalTheory.JacquetExact.exists_finset_of_mem_twKer h1
  have hH : ∀ a, ∃ H : Subgroup (GL (Fin (d a)) k), H ≤ unipRad k (e' a) ∧
      IsCompact (H : Set (GL (Fin (d a)) k)) ∧ ∀ u ∈ S, u a ∈ H := by
    intro a
    have hN : unipRad k (e' a) = unipOf k fun i => ((blk (e' a) i).val : ℤ) :=
      unipRad_eq_unipOf k fun i j => by simp
    obtain ⟨H, hle, hc, hSH⟩ := GlobalTheory.UnipCompact.exists_compact_subgroup k (Fin (d a)) _
      (S.image fun u => u a) (by
        intro u hu
        obtain ⟨u', hu', rfl⟩ := Finset.mem_image.1 hu
        have hm : u' a ∈ unipRad k (e' a) := hS u' hu' a (Set.mem_univ a)
        exact hN ▸ hm)
    exact ⟨H, hle.trans hN.ge, hc, fun u hu => hSH _ (Finset.mem_image_of_mem _ hu)⟩
  choose H hle hc hSH using hH
  let H' : Subgroup (Levi k fun a => Fin (d a)) := Subgroup.pi Set.univ H
  have hc' : IsCompact (H' : Set (Levi k fun a => Fin (d a))) := by
    have : (H' : Set (Levi k fun a => Fin (d a))) = Set.pi Set.univ fun a => (H a : Set _) := rfl
    rw [this]
    exact isCompact_univ_pi hc
  have hle' : H' ≤ relUnipD k e' := fun u hu a _ => hle a (hu a (Set.mem_univ a))
  refine (Submodule.Quotient.mk_eq_zero _).2 ?_
  exact GlobalTheory.IwahoriInj.twKer_mono hle'
    (GlobalTheory.JacquetExact.mem_twKer_of_compact hτ f hf hc' (h2 H' fun u hu a _ => hSH a u hu))

theorem isSubquotient_relJacD : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (s : ℕ) (d : Fin s → ℕ) (t : Fin s → ℕ) (d' : ∀ a, Fin (t a) → ℕ)
    (e' : ∀ a, (Σ b, Fin (d' a b)) ≃ Fin (d a)) (V W : Type) [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (Levi k fun a => Fin (d a)) V)
    (τ : Representation ℂ (Levi k fun a => Fin (d a)) W),
    IsSmooth τ → IsSubquotient σ τ → IsSubquotient (relJacD e' σ) (relJacD e' τ) := by
  intro k _ _ _ _ s d t d' e' V W _ _ _ _ σ τ hτ h
  obtain ⟨S, f, hf⟩ := h
  let ι : S.toRepresentation.IntertwiningMap τ := ⟨S.toSubmodule.subtype, fun _ => rfl⟩
  exact (IsSubquotient.of_surjective _ (relJacMap_surjective e' f hf)).trans
    (.of_injective _ (relJacMap_injective e' hτ ι Subtype.val_injective))

end GlobalTheory.JacStagesExact
end
end

section

open PowerSeries GlobalTheory.BK

theorem _root_.GlobalTheory.T.eulerDerivation_preserves_breuilKisin_sum_submodule : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (κ : Type) [Fintype κ] [DecidableEq κ] (η H : ℕ) (D₁ : BKDat O K l e a ι η H) (D₂ : BKDat O K l e a κ η H) (F : BKHom D₁ D₂) (A' b : ℕ), GlobalTheory.IndefiniteRowSideFullHecke.ImageStableDegreeBounds.Reduction O K l e a → ∀ x ∈ GlobalTheory.CokerL.Tsub F A' b, D₂.conn x ∈ GlobalTheory.CokerL.Tsub F A' b := by
  first | exact @GlobalTheory.CokerL.Tsub_conn | exact GlobalTheory.CokerL.Tsub_conn | (intros; apply GlobalTheory.CokerL.Tsub_conn <;> assumption)
end

section

open PowerSeries GlobalTheory.BK

theorem _root_.GlobalTheory.T.isotypicProjector_mem_isotypicPart_explicit : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (P : PhiMod O K l e a ι) (Δ : Descent P) (c : ZMod e) (v : Vec K a ι), GlobalTheory.CokerL.isoProj Δ c v ∈ Δ.isotypic c := by
  first | exact @GlobalTheory.CokerL.isoProj_mem_isotypic' | exact GlobalTheory.CokerL.isoProj_mem_isotypic' | (intros; apply GlobalTheory.CokerL.isoProj_mem_isotypic' <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

noncomputable section

namespace GlobalTheory.BKFinLevelKer

theorem mk_eq_of_smul {G : Type} [Group G] {LL : Type} [Field LL] {O : Type} [CommRing O] [Algebra O LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module O V] [IsScalarTower O LL V]
    {ρ : Representation LL G V} (L : Lattice (O := O) ρ) (ϖ : O) (r : ℕ) (π : LL) (hπ : π ≠ 0)
    (hpr : ∀ v : V, π ^ r • v = ϖ ^ r • v) (u v w : V) (hu : u ∈ L.T) (hv : v ∈ L.T)
    (hvw : π⁻¹ ^ r • u - w ∈ L.T) (hyw : v = π ^ r • w) :
    (Submodule.Quotient.mk (⟨v, hv⟩ : ↥L.T) : ↥L.T ⧸ (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥L.T)) =
      Submodule.Quotient.mk ⟨u, hu⟩ := by
  rw [Submodule.Quotient.eq]
  have ht : (⟨v, hv⟩ : ↥L.T) - ⟨u, hu⟩ = ϖ ^ r • (-(⟨_, hvw⟩ : ↥L.T)) := by
    apply Subtype.ext
    simp only [Submodule.coe_sub, Submodule.coe_smul, Submodule.coe_neg]
    rw [← hpr, smul_neg, smul_sub, smul_smul, ← mul_pow, mul_inv_cancel₀ hπ, one_pow, one_smul, hyw]
    abel
  rw [ht]
  exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) Submodule.mem_top

theorem hfQ_of_ioL_mem_HfD : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ (A : GRep ↥(GK K) ℚ_[l] LL O) (LA : Lattice (O := O) A.ρ) (ϖ : O), Irreducible ϖ → ∀ (r : ℕ) (hI : StableSub LA (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥LA.T)) (c : ↥(GK K) → ↥LA.T ⧸ (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥LA.T)), (fun g => GlobalTheory.BKFinLevel.ioL LA ϖ r (c g)) ∈ HfD (P.PD K) LA → c ∈ HfQ (P.PD K) LA _ hI := by
  intro l _ P K LL _ _ _ O _ _ hO A LA ϖ hϖ r hI c hc
  obtain ⟨π, hπdef⟩ : ∃ π : LL, π = algebraMap O LL ϖ := ⟨_, rfl⟩
  have hπ : π ≠ 0 := by
    obtain ⟨⟨hDom, hDVR, hFr⟩, -, -, -, -⟩ := hO
    haveI := hDom; haveI := hDVR; haveI := hFr
    intro h
    exact hϖ.ne_zero (IsFractionRing.injective O LL (by rw [← hπdef, h, map_zero]))
  clear hO

  obtain ⟨_, ⟨z, hz, rfl⟩, _, ⟨xq, rfl⟩, hsum⟩ := Submodule.mem_sup.1 hc
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ xq
  obtain ⟨w, hwdef⟩ : ∃ w : ↥(GK K) → A.V, w = z + fun g => A.ρ g x - x := ⟨_, rfl⟩
  have hcob : (fun g => A.ρ g x - x) ∈ finiteCocycles (P.PD K) A.ρ := by
    refine ⟨⟨?_, fun g h => ?_⟩, x ⊗ₜ[ℚ_[l]] (1 : _), fun g => ?_⟩
    · simp_rw [sub_eq_add_neg]
      exact (A.cont x).add continuous_const
    · simp only [map_mul, Module.End.mul_apply, map_sub]
      abel
    · simp [actVB, sub_tmul]
  have hw : w ∈ finiteCocycles (P.PD K) A.ρ := hwdef ▸ (finiteCocycles (P.PD K) A.ρ).add_mem hz hcob

  choose ch hch using fun g => Submodule.Quotient.mk_surjective _ (c g)

  have hpt : ∀ g, (π⁻¹ ^ r • ((ch g : ↥LA.T) : A.V)) - w g ∈ LA.T := by
    intro g
    have key : GlobalTheory.BKFinLevel.ioL LA ϖ r (c g) = Submodule.Quotient.mk (p := LA.T) (w g) :=
      by rw [← congrFun hsum g, hwdef]; rfl
    have h2 : (Submodule.Quotient.mk (π⁻¹ ^ r • ((ch g : ↥LA.T) : A.V)) : A.V ⧸ LA.T) =
        Submodule.Quotient.mk (w g) :=
      hπdef ▸ (GlobalTheory.BKFinLevel.ioL_mk LA ϖ r (ch g)).symm.trans ((congrArg _ (hch g)).trans key)
    exact (Submodule.Quotient.eq _).1 h2
  obtain ⟨y, hydef⟩ : ∃ y : ↥(GK K) → A.V, y = fun g => π ^ r • w g := ⟨_, rfl⟩
  have hyf : y ∈ finiteCocycles (P.PD K) A.ρ := by
    have h := (finiteCocycles (P.PD K) A.ρ).smul_mem (π ^ r) hw
    subst hydef; exact h
  have hpr : ∀ v : A.V, π ^ r • v = ϖ ^ r • v := fun v => by
    rw [hπdef, ← map_pow, algebraMap_smul]
  have hyT : ∀ g, y g ∈ LA.T := by
    intro g
    have : y g = ((ch g : ↥LA.T) : A.V) - ϖ ^ r • ((π⁻¹ ^ r • ((ch g : ↥LA.T) : A.V)) - w g) := by
      rw [← hpr, smul_sub, smul_smul, ← mul_pow, mul_inv_cancel₀ hπ, one_pow, one_smul]
      simp [hydef]
    rw [this]
    exact LA.T.sub_mem (ch g).2 (LA.T.smul_mem _ (hpt g))
  have hyZ : y ∈ latticeCocycles LA := ⟨hyf.1, fun g _ => hyT g⟩
  refine Submodule.mem_sup_left ⟨⟨y, hyZ⟩, ⟨hyZ, hyf⟩, ?_⟩
  funext g
  have e : (redT LA (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥LA.T) ⟨y, hyZ⟩) g =
      Submodule.Quotient.mk (⟨y g, hyT g⟩ : ↥LA.T) := rfl
  rw [e, ← hch g]
  exact mk_eq_of_smul LA ϖ r π hπ hpr _ _ (w g) (ch g).2 (hyT g) (hpt g) (by rw [hydef])

end GlobalTheory.BKFinLevelKer
end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

noncomputable section

namespace GlobalTheory.BKFinLevel.NatCup

section Lifts

variable {G : Type} [Group G] {LL : Type} [Field LL] {O : Type} [CommRing O] [Algebra O LL]
  {V : Type} [AddCommGroup V] [Module LL V] [Module O V] [IsScalarTower O LL V]
  {ρ : Representation LL G V}

theorem liftQ_mem_lat (L : Lattice (O := O) ρ) (I : Submodule O ↥L.T) (x : ↥L.T ⧸ I) :
    Formalism.MainNotions.LocalSituation.liftQ L I x ∈ L.T :=
  (Submodule.Quotient.mk_surjective I x).choose.2

theorem mk_liftQ_lat (L : Lattice (O := O) ρ) (I : Submodule O ↥L.T) (x : ↥L.T ⧸ I) :
    (Submodule.Quotient.mk ⟨Formalism.MainNotions.LocalSituation.liftQ L I x, liftQ_mem_lat L I x⟩ : ↥L.T ⧸ I) = x :=
  (Submodule.Quotient.mk_surjective I x).choose_spec

theorem mk_liftD_lat (L : Lattice (O := O) ρ) (c : V ⧸ L.T) :
    (Submodule.Quotient.mk (liftD L c) : V ⧸ L.T) = c :=
  (Submodule.Quotient.mk_surjective L.T c).choose_spec

theorem mem_span_pow_smul_top (L : Lattice (O := O) ρ) (a : O) (x : ↥L.T) :
    x ∈ (Ideal.span {a} • ⊤ : Submodule O ↥L.T) ↔ ∃ y : ↥L.T, x = a • y := by
  rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists]
  constructor
  · rintro ⟨y, -, rfl⟩; exact ⟨y, rfl⟩
  · rintro ⟨y, rfl⟩; exact ⟨y, Submodule.mem_top, rfl⟩

theorem inv_pow_mul_pow_mem (ϖ : O) (r : ℕ) :
    ∃ e : O, (algebraMap O LL ϖ)⁻¹ ^ r * (algebraMap O LL ϖ) ^ r = algebraMap O LL e := by
  rcases eq_or_ne (algebraMap O LL ϖ) 0 with h0 | h0
  · rcases Nat.eq_zero_or_pos r with hr | hr
    · exact ⟨1, by simp [hr]⟩
    · exact ⟨0, by simp [h0, zero_pow hr.ne']⟩
  · exact ⟨1, by rw [← mul_pow, inv_mul_cancel₀ h0, one_pow, map_one]⟩

theorem pair_shift {V' : Type} [AddCommGroup V'] [Module LL V'] (m : V →ₗ[LL] V' →ₗ[LL] LL)
    (f : V' →ₗ[LL] V') (a t â : V) (w y : V') (c π k u v : LL) (hâ : â = a + π • t)
    (hk : c * π = k) (hu : m a (f (w - c • y)) = u) (hv : m t (f y) = v) :
    u - k * v = m a (f w) - c * m â (f y) := by
  subst hâ hk hu hv
  simp only [map_sub, map_add (f := _), map_smul, LinearMap.sub_apply, LinearMap.add_apply,
    LinearMap.smul_apply, smul_eq_mul]
  ring

end Lifts

end GlobalTheory.BKFinLevel.NatCup

namespace GlobalTheory.BKFinLevel


open GlobalTheory.BKFinLevel.NatCup in
theorem cobO_cupLD_ioL_iff : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ L1 : Lattice (O := O) (charRep (cycLL (P.PD K) LL)), L1.T = LinearMap.range (Algebra.linearMap O LL) → ∀ (A A' : GRep ↥(GK K) ℚ_[l] LL O) (LA : Lattice (O := O) A.ρ) (LA' : Lattice (O := O) A'.ρ) (m : A.V →ₗ[LL] A'.V →ₗ[LL] LL), IsDualLat1 (P.PD K) LA LA' m → ∀ (ϖ : O) (r : ℕ) (d : ↥(latticeCocycles LA)) (c' : ↥(GK K) → ↥LA'.T ⧸ (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥LA'.T)), CobO (P.PD K) L1 (cupLD LA' m (d : ↥(GK K) → A.V) (fun g => GlobalTheory.BKFinLevel.ioL LA' ϖ r (c' g))) ↔ CobO (P.PD K) L1 (GlobalTheory.BKFinLevel.cupQ LA LA' m ϖ r (redT LA _ d) c') := by
  intro l _ P K LL _ _ _ O _ _ _ L1 hL1 A A' LA LA' m hd ϖ r d c'
  have key : ∀ x, (Submodule.Quotient.mk (cupLD LA' m (d : ↥(GK K) → A.V)
      (fun g => ioL LA' ϖ r (c' g)) x) : LL ⧸ L1.T) =
      Submodule.Quotient.mk (cupQ LA LA' m ϖ r (redT LA _ d) c' x) := by
    rintro ⟨g, h⟩
    rw [Submodule.Quotient.eq, hL1]
    obtain ⟨e, he⟩ := inv_pow_mul_pow_mem (LL := LL) ϖ r

    have hyT := liftQ_mem_lat LA' _ (c' h)
    have hw : liftD LA' (ioL LA' ϖ r (c' h)) -
        (algebraMap O LL ϖ)⁻¹ ^ r • Formalism.MainNotions.LocalSituation.liftQ LA' _ (c' h) ∈ LA'.T := by
      have h2 : ioL LA' ϖ r (c' h) = Submodule.Quotient.mk
          ((algebraMap O LL ϖ)⁻¹ ^ r • Formalism.MainNotions.LocalSituation.liftQ LA' _ (c' h)) := by
        conv_lhs => rw [← mk_liftQ_lat LA' _ (c' h)]
        rfl
      exact (Submodule.Quotient.eq _).1 ((mk_liftD_lat LA' _).trans h2)

    have haT : (d : ↥(GK K) → A.V) g ∈ LA.T := d.2.2 g (Set.mem_univ g)
    have hred : (Submodule.Quotient.mk ⟨Formalism.MainNotions.LocalSituation.liftQ LA _ (redT LA _ d g),
        liftQ_mem_lat LA _ _⟩ : ↥LA.T ⧸ (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥LA.T)) =
        Submodule.Quotient.mk ⟨(d : ↥(GK K) → A.V) g, haT⟩ := mk_liftQ_lat LA _ _
    obtain ⟨t, ht⟩ := (mem_span_pow_smul_top LA _ _).1 ((Submodule.Quotient.eq _).1 hred)
    have ht' : Formalism.MainNotions.LocalSituation.liftQ LA (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥LA.T) (redT LA (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥LA.T) d g) =
        (d : ↥(GK K) → A.V) g + (algebraMap O LL ϖ) ^ r • (t : A.V) := by
      have := congrArg (fun z : ↥LA.T => (z : A.V)) ht
      simp only [Submodule.coe_sub, Submodule.coe_smul] at this
      have hs : (algebraMap O LL ϖ) ^ r • (t : A.V) = ϖ ^ r • (t : A.V) := by
        rw [← map_pow, algebraMap_smul]
      rw [hs]
      exact (sub_eq_iff_eq_add').1 this
    have hw2 : A'.ρ g (liftD LA' (ioL LA' ϖ r (c' h)) - (algebraMap O LL ϖ)⁻¹ ^ r • Formalism.MainNotions.LocalSituation.liftQ LA' (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥LA'.T) (c' h)) ∈ LA'.T := LA'.stable g _ hw
    have hy2 : A'.ρ g (Formalism.MainNotions.LocalSituation.liftQ LA' (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥LA'.T) (c' h)) ∈ LA'.T := LA'.stable g _ hyT
    have hb1' : ∃ b : O, m ((d : ↥(GK K) → A.V) g) (A'.ρ g (liftD LA' (ioL LA' ϖ r (c' h)) - (algebraMap O LL ϖ)⁻¹ ^ r • Formalism.MainNotions.LocalSituation.liftQ LA' (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥LA'.T) (c' h))) = algebraMap O LL b := (hd.2 _).1 hw2 _ haT
    have hb2' : ∃ b : O, m (t : A.V) (A'.ρ g (Formalism.MainNotions.LocalSituation.liftQ LA' (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥LA'.T) (c' h))) = algebraMap O LL b := (hd.2 _).1 hy2 _ t.2
    obtain ⟨b1, hb1⟩ := hb1'
    obtain ⟨b2, hb2⟩ := hb2'
    refine ⟨b1 - e * b2, ?_⟩
    show algebraMap O LL (b1 - e * b2) =
      m ((d : ↥(GK K) → A.V) g) (A'.ρ g (liftD LA' (ioL LA' ϖ r (c' h)))) -
        (algebraMap O LL ϖ)⁻¹ ^ r * m (Formalism.MainNotions.LocalSituation.liftQ LA (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥LA.T) (redT LA (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥LA.T) d g))
          (A'.ρ g (Formalism.MainNotions.LocalSituation.liftQ LA' _ (c' h)))
    have hsplit : algebraMap O LL (b1 - e * b2) =
        algebraMap O LL b1 - algebraMap O LL e * algebraMap O LL b2 := by
      rw [map_sub, map_mul]
    exact hsplit.trans (pair_shift m (A'.ρ g) _ _ _ _ _ _ _ _ _ _ ht' he hb1 hb2)
  unfold CobO
  exact Iff.of_eq (congrArg (fun z => z ∈ ReciprocityTheory.Def.B2 (repD L1) ⊤) (funext key))

end GlobalTheory.BKFinLevel
end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory.BKFinLevelCocycle

theorem ioL_actQ {G : Type} [Group G] {LL : Type} [Field LL] {O : Type} [CommRing O] [Algebra O LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module O V] [IsScalarTower O LL V]
    {ρ : Representation LL G V} (L : Lattice (O := O) ρ) (ϖ : O) (r : ℕ)
    (hI : StableSub L (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥L.T)) (g : G)
    (x : ↥L.T ⧸ (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥L.T)) :
    GlobalTheory.BKFinLevel.ioL L ϖ r (actQ L _ hI g x) = actD L g (GlobalTheory.BKFinLevel.ioL L ϖ r x) := by
  induction x using Submodule.Quotient.induction_on with
  | H y =>
    simp only [actQ, Submodule.mapQ_apply, GlobalTheory.BKFinLevel.ioL_mk, actD, actT]
    congr 1
    simp only [LinearMap.coe_restrictScalars, map_smul]
    rfl

theorem ioL_mem_Z1D : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ (A : GRep ↥(GK K) ℚ_[l] LL O) (LA : Lattice (O := O) A.ρ) (ϖ : O) (r : ℕ) (hI : StableSub LA (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥LA.T)) (c : ↥(GK K) → ↥LA.T ⧸ (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥LA.T)), c ∈ quotientCocycles LA _ hI → (fun g => GlobalTheory.BKFinLevel.ioL LA ϖ r (c g)) ∈ divisibleCocycles LA := by
  intro l _ P K LL _ _ _ O _ _ hO A LA ϖ r hI c hc
  refine ⟨hc.1.comp _, fun g h => ?_⟩
  simp only [hc.2 g h, map_add (f := _), ioL_actQ]

end GlobalTheory.BKFinLevelCocycle
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

noncomputable section

namespace GlobalTheory.BKOrthRed

section Gen

variable {G : Type} [Group G] {LL : Type} [Field LL] {O : Type} [CommRing O] [Algebra O LL]
  {V : Type} [AddCommGroup V] [Module LL V] [Module O V] [IsScalarTower O LL V]
  {ρ : Representation LL G V}

theorem mem_span_smul_top (L : Lattice (O := O) ρ) (a : O) (x : ↥L.T) :
    x ∈ (Ideal.span {a} • ⊤ : Submodule O ↥L.T) ↔ ∃ y : ↥L.T, x = a • y := by
  rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists]
  constructor
  · rintro ⟨y, -, rfl⟩; exact ⟨y, rfl⟩
  · rintro ⟨y, rfl⟩; exact ⟨y, Submodule.mem_top, rfl⟩

theorem liftQ_eq (L : Lattice (O := O) ρ) (ϖ : O) (r : ℕ) (v : V) (hv : v ∈ L.T) :
    ∃ t : ↥L.T, Formalism.MainNotions.LocalSituation.liftQ L (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥L.T)
      (Submodule.Quotient.mk ⟨v, hv⟩) = v + (algebraMap O LL ϖ) ^ r • (t : V) := by
  have hs := (Submodule.Quotient.mk_surjective (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥L.T)
    (Submodule.Quotient.mk ⟨v, hv⟩)).choose_spec
  obtain ⟨t, ht⟩ := (mem_span_smul_top L _ _).1 ((Submodule.Quotient.eq _).1 hs)
  refine ⟨t, ?_⟩
  have h2 := congrArg (fun x : ↥L.T => (x : V)) ht
  simp only [Submodule.coe_sub, Submodule.coe_smul] at h2
  unfold Formalism.MainNotions.LocalSituation.liftQ
  rw [← map_pow, algebraMap_smul, ← h2]
  abel

end Gen

section Gal

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR] [TopologicalSpace Qp]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [IsTopologicalRing LL]
    {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra O LL]
    [IsFractionRing O LL]

theorem hfQ_lift {A : GRep G Qp LL O} (LA : Lattice (O := O) A.ρ) (I : Submodule O ↥LA.T)
    (hI : StableSub LA I) (c : G → ↥LA.T ⧸ I) (hc : c ∈ HfQ PD LA I hI) :
    ∃ a : G → A.V, a ∈ finiteCocycles PD A.ρ ∧ ∀ g, ∃ h : a g ∈ LA.T, c g = Submodule.Quotient.mk ⟨a g, h⟩ := by
  rw [HfQ, Submodule.mem_sup] at hc
  obtain ⟨y, hy, z, hz, rfl⟩ := hc
  obtain ⟨a0, ha0, rfl⟩ := hy
  obtain ⟨x, rfl⟩ := hz
  obtain ⟨xh, rfl⟩ := Submodule.Quotient.mk_surjective I x
  refine ⟨(a0 : G → A.V) + cob A.ρ (xh : A.V), (finiteCocycles PD A.ρ).add_mem ha0.2 (Formalism.MainNotions.BlochKatoDuality.Br.coboundary_mem_finite_cocycles PD A _),
    fun g => ⟨LA.T.add_mem (a0.2.2 g trivial) (LA.T.sub_mem (LA.stable g _ xh.2) xh.2), ?_⟩⟩
  show Submodule.Quotient.mk (evT LA g a0) + (actQ LA I hI g (Submodule.Quotient.mk xh) - Submodule.Quotient.mk xh) = _
  rw [actQ, Submodule.mapQ_apply, ← Submodule.Quotient.mk_sub, ← Submodule.Quotient.mk_add]
  congr 1

end Gal

theorem cupQ_cobO_of_bkA : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l), Formalism.MainNotions.N.bkACore (P.PD K) → ∀ (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ L1 : Lattice (O := O) (charRep (cycLL (P.PD K) LL)), L1.T = LinearMap.range (Algebra.linearMap O LL) → ∀ (A A' : GRep ↥(GK K) ℚ_[l] LL O) (LA : Lattice (O := O) A.ρ) (LA' : Lattice (O := O) A'.ρ) (m : A.V →ₗ[LL] A'.V →ₗ[LL] LL), IsDR (P.PD K) A.ρ → IsDualLat1 (P.PD K) LA LA' m → ∀ (ϖ : O) (r : ℕ) (hI : StableSub LA (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥LA.T)) (hI' : StableSub LA' (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥LA'.T)), ∀ c ∈ HfQ (P.PD K) LA _ hI, ∀ c' ∈ HfQ (P.PD K) LA' _ hI', CobO (P.PD K) L1 (GlobalTheory.BKFinLevel.cupQ LA LA' m ϖ r c c') := by
  intro l _ P K hA LL _ _ _ O _ _ hO L1 hL1 A A' LA LA' m hDR hd ϖ r hI hI' c hc c' hc'
  have hA' := hA LL O hO
  obtain ⟨⟨hDom, hDVR, hFr⟩, hfd, hmt, htr, hopen⟩ := hO
  haveI := hDom; haveI := hDVR; haveI := hFr; haveI := htr
  obtain ⟨a, ha, hag⟩ := hfQ_lift (P.PD K) LA _ hI c hc
  obtain ⟨b, hb, hbg⟩ := hfQ_lift (P.PD K) LA' _ hI' c' hc'
  obtain ⟨f, hf, hfd1⟩ := ((hA' A A' m hDR hd.1).1 a ha.1).1 ha b hb
  set s : LL := (algebraMap O LL ϖ)⁻¹ ^ r with hs
  have hcob : CobL (P.PD K) (fun x => s * cupL A'.ρ m a b x) := by
    refine ⟨s • f, continuous_const.mul hf, ?_⟩
    rw [map_smul, hfd1]
    rfl
  have hred := Formalism.MainNotions.BlochKatoDuality.Br.red_cob (P.PD K) hopen L1 hL1 _ hcob
  refine (Formalism.MainNotions.BlochKatoDuality.Br.cobO_congr (P.PD K) L1 _ _ ?_).2 hred
  rintro ⟨g, h⟩
  obtain ⟨hag1, hcg⟩ := hag g
  obtain ⟨hbh1, hch⟩ := hbg h
  obtain ⟨t, ht⟩ := liftQ_eq LA ϖ r (a g) hag1
  obtain ⟨t', ht'⟩ := liftQ_eq LA' ϖ r (b h) hbh1
  obtain ⟨u1, hu1⟩ := (hd.2 _).1 (LA'.stable g _ hbh1) t t.2
  obtain ⟨u2, hu2⟩ := (hd.2 _).1 (LA'.stable g _ t'.2) (a g) hag1
  obtain ⟨u3, hu3⟩ := (hd.2 _).1 (LA'.stable g _ t'.2) t t.2
  have ho : ∃ o : O, algebraMap O LL o = s * (algebraMap O LL ϖ) ^ r := by
    rw [hs, ← mul_pow]
    rcases eq_or_ne (algebraMap O LL ϖ) 0 with h0 | h0
    · exact ⟨0 ^ r, by rw [h0, inv_zero, zero_mul, map_pow, map_zero]⟩
    · exact ⟨1, by rw [inv_mul_cancel₀ h0, one_pow, map_one]⟩
  obtain ⟨o, ho⟩ := ho
  rw [Submodule.Quotient.eq, hL1]
  refine ⟨o * (u1 + u2 + ϖ ^ r * u3), ?_⟩
  show _ = s * m (Formalism.MainNotions.LocalSituation.liftQ LA _ (c g)) (A'.ρ g (Formalism.MainNotions.LocalSituation.liftQ LA' _ (c' h))) - s * m (a g) (A'.ρ g (b h))
  rw [hcg, hch, ht, ht']
  simp only [Algebra.linearMap_apply, map_mul, map_add (f := _), map_pow, map_smul, LinearMap.add_apply,
    LinearMap.smul_apply, smul_eq_mul]
  rw [← hu1, ← hu2, ← hu3, ho]
  ring

end GlobalTheory.BKOrthRed
end
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.CuspGeneric

namespace GlobalTheory.CuspGeneric

theorem avg_add_of_per : ∀ (G : Type) [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] (Γ : AddSubgroup G), IsCoLat Γ →
    ∀ Φ Φ' : G → ℂ, Per Γ Φ → Per Γ Φ' → avg Γ (fun x => Φ x + Φ' x) = avg Γ Φ + avg Γ Φ' := by
  intro G _ _ _ _ _ _ Γ hΓ Φ Φ' h h'
  letI : MeasurableSpace G := borel G
  haveI : BorelSpace G := ⟨rfl⟩
  obtain ⟨μ, 𝓕, hμ, hF, h1⟩ := GlobalTheory.T.exists_fundamentalDomain_mass_one_cocompactLattice G Γ hΓ
  have hs : Per Γ (fun x => Φ x + Φ' x) :=
    ⟨h.1.add h'.1, fun γ hγ x => by simp only [h.2 γ hγ x, h'.2 γ hγ x]⟩
  obtain ⟨-, -, i1, e1⟩ := GlobalTheory.T.setIntegral_fundamentalDomain_eq_mass_mul_average G Γ hΓ μ 𝓕 hμ hF Φ h
  obtain ⟨-, -, i2, e2⟩ := GlobalTheory.T.setIntegral_fundamentalDomain_eq_mass_mul_average G Γ hΓ μ 𝓕 hμ hF Φ' h'
  obtain ⟨-, -, -, e3⟩ := GlobalTheory.T.setIntegral_fundamentalDomain_eq_mass_mul_average G Γ hΓ μ 𝓕 hμ hF _ hs
  rw [h1] at e1 e2 e3
  simp only [ENNReal.toReal_one, Complex.ofReal_one, one_mul] at e1 e2 e3
  rw [← e1, ← e2, ← e3]
  exact integral_add i1 i2

end GlobalTheory.CuspGeneric
end
