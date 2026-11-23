module

public import Formalism.LocalToGlobal.IndefiniteReal.Bundle018
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle003
public import Formalism.LocalToGlobal.IndefiniteReal.PeterssonHilbertSpace
public import Formalism.LocalToGlobal.IndefiniteReal.EvalTieTOne
public import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
public import Formalism.LocalToGlobal.IndefiniteReal.SchurOrthogonality
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

@[expose] public section

section

noncomputable section

open NumberField IsDedekindDomain
open Formalism.L2.Theta
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory
open scoped TensorProduct

namespace Formalism.IndefR.principalLevelFrame

section Indep

variable {A : Type} [AddCommGroup A] [Module ℂ A]

theorem hp_add_right {C : Submodule ℂ A} {ip : A → A → ℂ} (hp : PeterssonHilbertSpace.IsHermPos C ip) (x y z : C) :
    ip x ((y : A) + z) = ip x y + ip x z := by
  have h1 := hp.herm (y + z) x
  have h2 := hp.herm y x
  have h3 := hp.herm z x
  have h4 := hp.add y z x
  simp only [Submodule.coe_add] at h1 h4
  rw [← h1, ← h2, ← h3, h4, map_add (f := _)]

theorem hp_zero_right {C : Submodule ℂ A} {ip : A → A → ℂ} (hp : PeterssonHilbertSpace.IsHermPos C ip) (x : C) : ip x (0 : A) = 0 := by
  have h := hp_add_right hp x 0 0
  simp only [ZeroMemClass.coe_zero, add_zero] at h
  linear_combination -h

theorem hp_sum_right {C : Submodule ℂ A} {ip : A → A → ℂ} (hp : PeterssonHilbertSpace.IsHermPos C ip) (x : C) {ι : Type}
    (s : Finset ι) (w : ι → C) : ip x (∑ i ∈ s, (w i : A)) = ∑ i ∈ s, ip x (w i) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp only [Finset.sum_empty]
    exact hp_zero_right hp x
  · intro a s ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha, ← ih]
    have h := hp_add_right hp x (w a) (∑ i ∈ s, w i)
    rw [Submodule.coe_sum] at h
    exact h

end Indep

section F

attribute [local instance] Formalism.BasicNotions.Host.cmStar

local instance instCMHostF (D : Formalism.BasicNotions.D7) : IsCMField D.host.E := D.host.isCMField_hostE

variable {D : Formalism.BasicNotions.D7} {n : ℕ}

theorem isotIn_le_of_intw {A : Type} [AddCommGroup A] [Module ℂ A] (ρ : Formalism.AUTREP.GAf D.host.E n →* Module.End ℂ A)
    (C : Submodule ℂ A) {π π' : Formalism.L2.NG.FinTyp D.host.E n} (T : π'.S →ₗ[ℂ] π.S) (hT : Intw π' π T)
    (hsurj : LinearMap.range T = ⊤) : isotIn ρ C π ≤ isotIn ρ C π' := by
  unfold isotIn
  refine iSup₂_le fun Φ hΦ => ?_
  have hr : LinearMap.range (Φ.comp T) = LinearMap.range Φ := by
    rw [LinearMap.range_comp, hsurj, Submodule.map_top]
  rw [← hr]
  refine le_iSup₂ (f := fun (Ψ : π'.S →ₗ[ℂ] A) (_ : IsEqvA ρ π' Ψ ∧ LinearMap.range Ψ ≤ C) => LinearMap.range Ψ)
    (Φ.comp T) ⟨?_, hr ▸ hΦ.2⟩
  intro h f
  simp only [LinearMap.comp_apply]
  rw [hT h f]
  exact hΦ.1 h (T f)

theorem isotIn_iso {A : Type} [AddCommGroup A] [Module ℂ A] (ρ : Formalism.AUTREP.GAf D.host.E n →* Module.End ℂ A)
    (C : Submodule ℂ A) {π π' : Formalism.L2.NG.FinTyp D.host.E n} (h : π.Iso π') : isotIn ρ C π = isotIn ρ C π' := by
  unfold Formalism.L2.NG.FinTyp.Iso Formalism.L2.NG.IsoRep at h
  obtain ⟨T, hT⟩ := h
  apply le_antisymm
  · refine isotIn_le_of_intw ρ C (T.symm : π'.S →ₗ[ℂ] π.S) ?_ (LinearMap.range_eq_top.2 T.symm.surjective)
    intro h f
    have key : T ⟨_, π.stable h _ (T.symm f).2⟩ = ⟨_, π'.stable h _ f.2⟩ := by
      apply Subtype.ext
      rw [hT h (T.symm f) ⟨_, π.stable h _ (T.symm f).2⟩ rfl, LinearEquiv.apply_symm_apply]
    exact T.symm_apply_eq.2 key.symm
  · refine isotIn_le_of_intw ρ C (T : π.S →ₗ[ℂ] π'.S) ?_ (LinearMap.range_eq_top.2 T.surjective)
    intro h f
    apply Subtype.ext
    exact hT h f ⟨_, π.stable h _ f.2⟩ rfl

variable {Y W : Formalism.BasicNotions.TH.HSp D} {SpY SpW : D.what₂.Tau → SPar}
variable (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ))

theorem isotL_iso (P : RowPsi W n) (M : Mult.DSModel W SpW) (J : Set (GA D W)) (χ : GA D W → ℂ)
    (e : (GA D W → ℂ) →ₗ[ℂ] (GA D W → ℂ)) {π π' : Formalism.L2.NG.FinTyp D.host.E n} (h : π.Iso π') :
    isotL θ P M J χ e π = isotL θ P M J χ e π' := by
  unfold isotL
  rw [isotIn_iso (actM P M) (Minf θ P M) h]



end F

end Formalism.IndefR.principalLevelFrame
end
end

section

noncomputable section

open NumberField IsDedekindDomain
open Formalism.L2.Theta
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory
open scoped TensorProduct

namespace Formalism.IndefR.principalLevelFrame

section Dec

attribute [local instance] Formalism.BasicNotions.Host.cmStar

local instance instCMHostD (D : Formalism.BasicNotions.D7) : IsCMField D.host.E := D.host.isCMField_hostE

variable {D : Formalism.BasicNotions.D7} {V : Formalism.BasicNotions.TH.HSp D} {n : ℕ} {Sp : D.what₂.Tau → SPar}
variable (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ))

def ActStable (P : RowPsi V n) (M : Mult.DSModel V Sp) : Prop :=
  ∀ h, ∀ T ∈ Minf θ P M, actM P M h T ∈ Minf θ P M

def IpInv (P : RowPsi V n) (M : Mult.DSModel V Sp) (μ : Measure (GA D V)) (𝓕 : Set (GA D V)) : Prop :=
  ∀ h, ∀ T ∈ Minf θ P M, ∀ T' ∈ Minf θ P M, Mult.ipM M μ 𝓕 (actM P M h T) (actM P M h T') = Mult.ipM M μ 𝓕 T T'

def HermPosLev (P : RowPsi V n) (M : Mult.DSModel V Sp) (μ : Measure (GA D V)) (𝓕 : Set (GA D V)) : Prop :=
  ∀ N : ℕ, 0 < N → PeterssonHilbertSpace.IsHermPos (Mult.Mult θ M (levN P N) (fun _ => 1)) (Mult.ipM M μ 𝓕)

def IsotDecomp (P : RowPsi V n) (M : Mult.DSModel V Sp) (J : Set (GA D V)) (χ : GA D V → ℂ)
    (e : (GA D V → ℂ) →ₗ[ℂ] (GA D V → ℂ)) (μ : Measure (GA D V)) (𝓕 : Set (GA D V)) : Prop :=
  Mult.goodPart θ M J χ e = ⨆ π : Formalism.L2.NG.FinTyp D.host.E n, isotL θ P M J χ e π ∧
    ∀ π π' : Formalism.L2.NG.FinTyp D.host.E n, ¬ π.Iso π' →
      ∀ x ∈ isotL θ P M J χ e π, ∀ y ∈ isotL θ P M J χ e π', Mult.ipM M μ 𝓕 x y = 0

end Dec

section DecProofs

attribute [local instance] Formalism.BasicNotions.Host.cmStar

local instance instCMHostD' (D : Formalism.BasicNotions.D7) : IsCMField D.host.E := D.host.isCMField_hostE

variable {D : Formalism.BasicNotions.D7} {V : Formalism.BasicNotions.TH.HSp D} {n : ℕ} {Sp : D.what₂.Tau → SPar}
variable {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)}
variable {P : RowPsi V n} {M : Mult.DSModel V Sp}

theorem isMultMap_mono {J J' : Set (GA D V)} {χ χ' : GA D V → ℂ} (hJ : J' ⊆ J) (hχ : ∀ k ∈ J', χ' k = χ k)
    {T : Mult.MMap M} (h : Mult.IsMultMap θ M J χ T) : Mult.IsMultMap θ M J' χ' T :=
  ⟨h.aut, h.cusp, fun v k hk g => by rw [h.lev v k (hJ hk) g, hχ k hk], h.equiv, h.cont⟩

theorem mult_mono {J J' : Set (GA D V)} {χ χ' : GA D V → ℂ} (hJ : J' ⊆ J) (hχ : ∀ k ∈ J', χ' k = χ k) :
    Mult.Mult θ M J χ ≤ Mult.Mult θ M J' χ' :=
  Submodule.span_mono fun _ hT => isMultMap_mono hJ hχ hT

theorem levN_mono (N m : ℕ) : levN P (N * m) ⊆ levN P N := by
  rintro _ ⟨κ, hκ, rfl⟩
  exact ⟨κ, Formalism.L2.NG.Cong.of_mul_left D.host.E n hκ, rfl⟩

abbrev LN (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (P : RowPsi V n) (M : Mult.DSModel V Sp) (N : ℕ) :
    Submodule ℂ (Mult.MMap M) :=
  Mult.Mult θ M (levN P (N + 1)) (fun _ => 1)

theorem LN_directed : Directed (· ≤ ·) (LN θ P M) := by
  intro i j
  have hpos : 1 ≤ (i + 1) * (j + 1) := Nat.one_le_iff_ne_zero.2 (by positivity)
  have e : (i + 1) * (j + 1) - 1 + 1 = (i + 1) * (j + 1) := Nat.sub_add_cancel hpos
  refine ⟨(i + 1) * (j + 1) - 1, ?_, ?_⟩
  · apply mult_mono
    · rw [e]
      exact levN_mono _ _
    · intros
      rfl
  · apply mult_mono
    · rw [e, mul_comm]
      exact levN_mono _ _
    · intros
      rfl

theorem mem_Minf {T : Mult.MMap M} : T ∈ Minf θ P M ↔ ∃ N, T ∈ LN θ P M N :=
  Submodule.mem_iSup_of_directed _ LN_directed

theorem LN_le_Minf (N : ℕ) : LN θ P M N ≤ Minf θ P M := le_iSup (LN θ P M) N

theorem common3 {x y z : Mult.MMap M} (hx : x ∈ Minf θ P M) (hy : y ∈ Minf θ P M) (hz : z ∈ Minf θ P M) :
    ∃ N, x ∈ LN θ P M N ∧ y ∈ LN θ P M N ∧ z ∈ LN θ P M N := by
  obtain ⟨a, ha⟩ := mem_Minf.1 hx
  obtain ⟨b, hb⟩ := mem_Minf.1 hy
  obtain ⟨c, hc⟩ := mem_Minf.1 hz
  obtain ⟨d, had, hbd⟩ := LN_directed (θ := θ) (P := P) (M := M) a b
  obtain ⟨k, hdk, hck⟩ := LN_directed (θ := θ) (P := P) (M := M) d c
  exact ⟨k, hdk (had ha), hdk (hbd hb), hck hc⟩

theorem mult_le_Minf {J : Set (GA D V)} {χ : GA D V → ℂ} (hl : LevOK P J χ) : Mult.Mult θ M J χ ≤ Minf θ P M := by
  obtain ⟨N0, hN0, h0⟩ := hl
  have e : N0 - 1 + 1 = N0 := Nat.sub_add_cancel hN0
  refine le_trans ?_ (LN_le_Minf (N0 - 1))
  apply mult_mono
  · rintro _ ⟨κ, hκ, rfl⟩
    rw [e] at hκ
    exact (h0 κ hκ).1
  · rintro _ ⟨κ, hκ, rfl⟩
    rw [e] at hκ
    exact (h0 κ hκ).2.symm

variable (μ : Measure (GA D V)) (𝓕 : Set (GA D V))

theorem hp3 (hHP : HermPosLev θ P M μ 𝓕) (x y z : Minf θ P M) :
    ∃ N, PeterssonHilbertSpace.IsHermPos (LN θ P M N) (Mult.ipM M μ 𝓕) ∧ (x : Mult.MMap M) ∈ LN θ P M N ∧
      (y : Mult.MMap M) ∈ LN θ P M N ∧ (z : Mult.MMap M) ∈ LN θ P M N := by
  obtain ⟨N, hx, hy, hz⟩ := common3 x.2 y.2 z.2
  exact ⟨N, hHP (N + 1) (Nat.succ_pos N), hx, hy, hz⟩

def ipA (hHP : HermPosLev θ P M μ 𝓕) : Minf θ P M →ₗ⋆[ℂ] Minf θ P M →ₗ[ℂ] ℂ :=
  LinearMap.mk₂'ₛₗ (starRingEnd ℂ) (RingHom.id ℂ) (fun x y => Mult.ipM M μ 𝓕 x y)
    (fun x x' y => by
      obtain ⟨N, hp, hx, hx', hy⟩ := hp3 μ 𝓕 hHP x x' y
      exact hp.add ⟨x, hx⟩ ⟨x', hx'⟩ ⟨y, hy⟩)
    (fun s x y => by
      obtain ⟨N, hp, hx, hy, -⟩ := hp3 μ 𝓕 hHP x y y
      exact hp.smul s ⟨x, hx⟩ ⟨y, hy⟩)
    (fun x y y' => by
      obtain ⟨N, hp, hx, hy, hy'⟩ := hp3 μ 𝓕 hHP x y y'
      have h1 := hp.herm ⟨(y : Mult.MMap M) + y', Submodule.add_mem _ hy hy'⟩ ⟨x, hx⟩
      have h2 := hp.herm ⟨y, hy⟩ ⟨x, hx⟩
      have h3 := hp.herm ⟨y', hy'⟩ ⟨x, hx⟩
      have h4 := hp.add ⟨y, hy⟩ ⟨y', hy'⟩ ⟨x, hx⟩
      simp only [Submodule.coe_add] at h1 h2 h3 h4 ⊢
      rw [← h1, ← h2, ← h3, h4, map_add (f := _)])
    (fun s x y => by
      obtain ⟨N, hp, hx, hy, -⟩ := hp3 μ 𝓕 hHP x y y
      have h1 := hp.herm ⟨s • (y : Mult.MMap M), Submodule.smul_mem _ s hy⟩ ⟨x, hx⟩
      have h2 := hp.herm ⟨y, hy⟩ ⟨x, hx⟩
      have h4 := hp.smul s ⟨y, hy⟩ ⟨x, hx⟩
      simp only [Submodule.coe_smul] at h1 h2 h4 ⊢
      rw [← h1, ← h2, h4, map_mul, Complex.conj_conj]
      rfl)

end DecProofs

end Formalism.IndefR.principalLevelFrame
end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory Formalism.L2.Theta Formalism.IndefR.Mult Formalism.L2.SG.RowDict
open scoped TensorProduct InnerProductSpace

namespace Formalism.IndefR.AutomorphicEvaluation

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {S : D.what₂.Tau → SPar}

section Pieces

variable (M : DSModel (D.sp.Y 0) S) (μ : Measure (GA D (D.sp.Y 0))) (𝓕 : Set (GA D (D.sp.Y 0)))
  (E : Submodule ℂ (MMap M)) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (G : GoodOp X) (ι : GA D (D.sp.Y 0) ≃* X.B.I.GA)
  (t : GA D (D.sp.Y 0)) (c : ℝ) (v₀ : M.Vec)

def SquareIntegrableTransfer : Prop :=
  ∀ F : GA D (D.sp.Y 0) → ℂ, Continuous F → (∀ γ ∈ GQ (D.sp.Y 0), ∀ x, F (γ * x) = F x) →
    MemLp F 2 (μ.restrict 𝓕) →
      MemLp (fun x => F (ι.symm x * t)) 2 (muX X) ∧
        ∫ x, ‖F (ι.symm x * t)‖ ^ 2 ∂(muX X) = c * ∫ x in 𝓕, ‖F x‖ ^ 2 ∂μ

def RphFix : Prop :=
  ∀ T ∈ E, ∀ hF : MemLp (fun x => ev M v₀ T (ι.symm x * t)) 2 (muX X),
    X.Rph (star (hF.toLp _)) = star (hF.toLp _)

def EvalIntoT : Prop :=
  ∀ T ∈ E, ∃ F : EEC X G, ((F : L2X X) =ᵐ[muX X] fun x => ev M v₀ T (ι.symm x * t)) ∧
    ‖(F : L2X X)‖ ^ 2 = c * (ipM M μ 𝓕 T T).re

def EvalOntoT : Prop :=
  ∀ F : EEC X G, ∃ T ∈ E, (F : L2X X) =ᵐ[muX X] fun x => ev M v₀ T (ι.symm x * t)

def EvalInjT : Prop :=
  ∀ T ∈ E, ((fun x => ev M v₀ T (ι.symm x * t)) =ᵐ[muX X] 0) → T = 0

end Pieces

theorem evalTieT_of (M : DSModel (D.sp.Y 0) S) (μ : Measure (GA D (D.sp.Y 0))) (𝓕 : Set (GA D (D.sp.Y 0)))
    (E : Submodule ℂ (MMap M)) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (G : GoodOp X) (ι : GA D (D.sp.Y 0) ≃* X.B.I.GA)
    (t : GA D (D.sp.Y 0)) (c : ℝ) (v₀ : M.Vec) (hv : ∀ τ, ‖(v₀ τ : M.H τ)‖ = 1)
    (hI : EvalIntoT M μ 𝓕 E X G ι t c v₀) (hO : EvalOntoT M E X G ι t v₀) (hJ : EvalInjT M E X ι t v₀) :
    EvalTieT M μ 𝓕 E X G ι t c := by
  classical
  choose Φ hΦ using fun T : E => hI T T.2
  have key : ∀ (T : E) (F : EEC X G), ((F : L2X X) =ᵐ[muX X] fun x => ev M v₀ (T : MMap M) (ι.symm x * t)) →
      Φ T = F := by
    intro T F hF
    apply Subtype.ext
    apply Lp.ext
    exact (hΦ T).1.trans hF.symm
  let L : E →ₗ[ℂ] EEC X G :=
    { toFun := Φ
      map_add' := fun T T' => by
        apply key
        have h1 := (hΦ T).1
        have h2 := (hΦ T').1
        have h3 := Lp.coeFn_add ((Φ T : EEC X G) : L2X X) ((Φ T' : EEC X G) : L2X X)
        refine (Filter.EventuallyEq.trans ?_ (h3.trans (h1.add h2))).trans ?_
        · simp only [Submodule.coe_add]; rfl
        · refine Filter.Eventually.of_forall fun x => ?_
          simp [ev_apply]
      map_smul' := fun a T => by
        rw [RingHom.id_apply]
        apply key
        have h1 := (hΦ T).1
        have h3 := Lp.coeFn_smul a ((Φ T : EEC X G) : L2X X)
        refine (Filter.EventuallyEq.trans ?_ (h3.trans (h1.const_smul a))).trans ?_
        · simp only [Submodule.coe_smul]; rfl
        · refine Filter.Eventually.of_forall fun x => ?_
          simp [ev_apply] }
  have hinj : Function.Injective L := by
    intro T T' h
    have hd : L (T - T') = 0 := by rw [map_sub, h, sub_self]
    have h1 := (hΦ (T - T')).1
    have h0 : ((fun x => ev M v₀ ((T - T' : E) : MMap M) (ι.symm x * t)) =ᵐ[muX X] 0) := by
      have hz : ((Φ (T - T') : EEC X G) : L2X X) = 0 := by
        have : Φ (T - T') = 0 := hd
        rw [this]; rfl
      have := Lp.coeFn_zero ℂ 2 (muX X)
      rw [← hz] at this
      exact h1.symm.trans this
    have := hJ ((T - T' : E) : MMap M) (T - T').2 h0
    exact sub_eq_zero.mp (Subtype.ext this)
  have hsurj : Function.Surjective L := by
    intro F
    obtain ⟨T, hT, hF⟩ := hO F
    exact ⟨⟨T, hT⟩, key ⟨T, hT⟩ F hF⟩
  exact ⟨v₀, hv, LinearEquiv.ofBijective L ⟨hinj, hsurj⟩, fun T => hΦ T⟩

section Assembly

variable {M : DSModel (D.sp.Y 0) S} {μ : Measure (GA D (D.sp.Y 0))} {𝓕 : Set (GA D (D.sp.Y 0))}
  {E : Submodule ℂ (MMap M)} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {G : GoodOp X} {ι : GA D (D.sp.Y 0) ≃* X.B.I.GA}
  {t : GA D (D.sp.Y 0)} {c : ℝ} {v₀ : M.Vec}

theorem norm_sq_toLp {f : X.B.I.GA → ℂ} (hf : MemLp f 2 (muX X)) :
    ‖(hf.toLp f : L2X X)‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 ∂(muX X) := by
  rw [@norm_sq_eq_re_inner ℂ, MeasureTheory.L2.inner_def]
  have h1 : (fun a => ⟪(hf.toLp f : L2X X) a, (hf.toLp f : L2X X) a⟫_ℂ) =
      fun a => (((‖(hf.toLp f : L2X X) a‖ ^ 2 : ℝ)) : ℂ) := by
    funext a; rw [inner_self_eq_norm_sq_to_K]; push_cast; rfl
  rw [h1, integral_complex_ofReal]
  simp only [RCLike.re_to_complex, Complex.ofReal_re]
  refine integral_congr_ae ?_
  filter_upwards [hf.coeFn_toLp] with a ha
  rw [ha]

theorem re_ipM_eq {T : MMap M} (hT : ∃ c', IsMultIP M μ 𝓕 T T c') (hv : ∀ τ, ‖(v₀ τ : M.H τ)‖ = 1) :
    (ipM M μ 𝓕 T T).re = ∫ x in 𝓕, ‖T v₀ x‖ ^ 2 ∂μ := by
  unfold ipM
  rw [dite_eq_left hT]
  obtain ⟨-, heq⟩ := hT.choose_spec v₀ v₀
  have hprod : ∏ τ, ⟪(v₀ τ : M.H τ), (v₀ τ : M.H τ)⟫_ℂ = 1 := by
    refine Finset.prod_eq_one fun τ _ => ?_
    rw [inner_self_eq_norm_sq_to_K, hv τ]
    simp
  rw [hprod, mul_one] at heq
  rw [← heq]
  have hpt : ∀ g, star (T v₀ g) * T v₀ g = ((‖T v₀ g‖ ^ 2 : ℝ) : ℂ) := fun g => by
    rw [Complex.star_def, Complex.conj_mul']
    push_cast
    rfl
  simp_rw [hpt]
  rw [integral_complex_ofReal]
  simp

end Assembly

end Formalism.IndefR.AutomorphicEvaluation

end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory Matrix
open Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.SchurOrthogonalityAlt
open scoped TensorProduct ContDiff InnerProductSpace

namespace Formalism.IndefR.AutomorphicEvaluation

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar}

variable (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ))


open Classical in
structure EqCont (M : DSModel V S) (T : MMap M) : Prop where
  equiv : ∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ (v : M.Vec) (w : M.sm τ),
    (w : M.H τ) = M.rep τ g (v τ) → T (Function.update v τ w) = rTr V (atTau θ V τ g) (T v)
  cont : ∀ τ (v : M.Vec) (x : GA D V), ∃ ℓ : M.H τ →ₗ[ℂ] ℂ, Sobolev₂ (lieAt V τ) (M.rep τ) ℓ ∧
    ∀ w : M.sm τ, ℓ w = T (Function.update v τ w) x

variable {θ}


open Classical in
theorem eqCont_of_mem {M : DSModel V S} {J : Set (GA D V)} {χ : GA D V → ℂ} {T : MMap M}
    (hT : T ∈ Mult θ M J χ) : EqCont θ M T := by
  induction hT using Submodule.span_induction with
  | mem T hT => exact ⟨hT.equiv, hT.cont⟩
  | zero =>
    refine ⟨fun τ g _ v w _ => ?_, fun τ v x => ⟨0, sobCont_zero, fun w => ?_⟩⟩
    · rw [MultilinearMap.zero_apply, MultilinearMap.zero_apply]; rfl
    · simp
  | add T T' _ _ h h' =>
    refine ⟨fun τ g hg v w hw => ?_, fun τ v x => ?_⟩
    · rw [MultilinearMap.add_apply, MultilinearMap.add_apply, h.equiv τ g hg v w hw, h'.equiv τ g hg v w hw]; rfl
    · obtain ⟨ℓ, hℓ, e⟩ := h.cont τ v x
      obtain ⟨ℓ', hℓ', e'⟩ := h'.cont τ v x
      exact ⟨ℓ + ℓ', sobCont_add hℓ hℓ', fun w => by
        rw [LinearMap.add_apply, e, e', MultilinearMap.add_apply, Pi.add_apply]⟩
  | smul a T _ h =>
    refine ⟨fun τ g hg v w hw => ?_, fun τ v x => ?_⟩
    · rw [MultilinearMap.smul_apply, MultilinearMap.smul_apply, h.equiv τ g hg v w hw]; rfl
    · obtain ⟨ℓ, hℓ, e⟩ := h.cont τ v x
      exact ⟨a • ℓ, sobCont_smul a hℓ, fun w => by
        rw [LinearMap.smul_apply, e, MultilinearMap.smul_apply, Pi.smul_apply]⟩




end Formalism.IndefR.AutomorphicEvaluation

end
end
