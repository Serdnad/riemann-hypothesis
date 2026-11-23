module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle312
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle332
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle313
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle315
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle330
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle316
public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.LeibnizOrders.ProdGPn
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle336
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle337
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicDoubleCosetDecomposition
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DerivativeOfProductInducedIso
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle317
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle089
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle338
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle302
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.SegmentCuspLines.Bundle001
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.LSegJacquet
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle335

@[expose] public section

section

open Matrix MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZSeg GlobalTheory.BZMir GlobalTheory.SplitWeil GlobalTheory.CompanionTheory.MirFourier GlobalTheory.CompanionTheory.BZOnto.PerpSmall ValuativeRel Zc
open scoped Topology
open GlobalTheory.CompanionTheory.MirPair


theorem _root_.GlobalTheory.T.shear_preserves_box_membership : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ} (g : GL (Fin (n + 1)) k), ∃ r : kˣ, valuation k (r : k) < 1 ∧ ∀ b ∈ box (n + 1) r, ∀ (t : kˣ) (x : Fin (n + 1) → k), ((g : Matrix (Fin (n + 1)) (Fin (n + 1)) k) *ᵥ (((shearGL n b : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) *ᵥ x) ∈ box (n + 1) t ↔ (g : Matrix (Fin (n + 1)) (Fin (n + 1)) k) *ᵥ x ∈ box (n + 1) t) := by
  first | exact @GlobalTheory.CompanionTheory.MirPair.ShearLat.main | exact GlobalTheory.CompanionTheory.MirPair.ShearLat.main | (intros; apply GlobalTheory.CompanionTheory.MirPair.ShearLat.main <;> assumption)
end

section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZRes Topology
open scoped TensorProduct

theorem _root_.GlobalTheory.T.closed_cell_inducing_character : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] {i j n : ℕ} (h : (i + 1) + j = n) (π₁ : Representation ℂ (GL (Fin (i + 1)) k) V) (π₂ : Representation ℂ (GL (Fin (j + 1)) k) W) (g : HGPg k h) (hq : (1 : GL (Fin (n + 1)) k) * ((g : Mir k n) : GL (Fin (n + 1)) k) * (1 : GL (Fin (n + 1)) k)⁻¹ ∈ parab k (two (stdSum (by omega : (i + 1) + (j + 1) = n + 1)))) (v : ⨂[ℂ] x, TwoT V W x), ((extTensor (GRep.tw (⟨V, π₁⟩ : GRep k (i + 1)) (((j + 1 : ℕ) : ℝ) / 2)).ρ (mtw (gres (⟨W, π₂⟩ : GRep k (j + 1))) (-((i + 1 : ℕ) : ℝ) / 2)).ρ).comp (gpProjg k h)) g (tE V W v) = tE V W (sQ (by omega : (i + 1) + (j + 1) = n + 1) π₁ π₂ ⟨_, hq⟩ v) := by
  first | exact @GlobalTheory.CompanionTheory.BZRes.hgp_twist_tE | exact GlobalTheory.CompanionTheory.BZRes.hgp_twist_tE | (intros; apply GlobalTheory.CompanionTheory.BZRes.hgp_twist_tE <;> assumption)
end

section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZRes Topology
open scoped TensorProduct

theorem _root_.GlobalTheory.T.open_cell_inducing_character : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] {i j : ℕ} (h : (i + 1) + (j + 1) = i + (j + 1) + 1) (π₁ : Representation ℂ (GL (Fin (i + 1)) k) V) (π₂ : Representation ℂ (GL (Fin (j + 1)) k) W) (g : HPG k i (j + 1)) (hq : wGL k h * ((g : Mir k (i + (j + 1))) : GL (Fin (i + (j + 1) + 1)) k) * (wGL k h)⁻¹ ∈ parab k (two (stdSum h))) (v : ⨂[ℂ] x, TwoT V W x), ((extTensor (mtw (gres (⟨V, π₁⟩ : GRep k (i + 1))) (((j + 1 : ℕ) : ℝ) / 2)).ρ (GRep.tw (⟨W, π₂⟩ : GRep k (j + 1)) (-((i + 1 : ℕ) : ℝ) / 2)).ρ).comp (pgProj k i (j + 1))) g (tE V W v) = tE V W (sQ h π₁ π₂ ⟨_, hq⟩ v) := by
  first | exact @GlobalTheory.CompanionTheory.BZRes.open_orbit_twist | exact GlobalTheory.CompanionTheory.BZRes.open_orbit_twist | (intros; apply GlobalTheory.CompanionTheory.BZRes.open_orbit_twist <;> assumption)
end

section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.CompanionTheory.BZNuPair

namespace GlobalTheory.CompanionTheory.BZNuPair.WhitCover

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {Y : Type} [AddCommGroup Y] [Module ℂ Y]

def toImg (ψ : AddChar k Circle) (d : Fin 2 → ℕ) (J : Representation ℂ (Levi k fun a => Fin (d a)) Y)
    (T : Subrepresentation J) : T.toSubmodule →ₗ[ℂ] (whitImg ψ d J T).toSubmodule :=
  LinearMap.codRestrict _ ((whitKer ψ d J).mkQ ∘ₗ T.toSubmodule.subtype) fun t => ⟨t, t.2, rfl⟩

def stepMap (ψ : AddChar k Circle) (d : Fin 2 → ℕ) (J : Representation ℂ (Levi k fun a => Fin (d a)) Y)
    (T T' : Subrepresentation J) :
    (T.toSubmodule ⧸ T'.toSubmodule.comap T.toSubmodule.subtype) →ₗ[ℂ]
      ((whitImg ψ d J T).toSubmodule ⧸
        (whitImg ψ d J T').toSubmodule.comap (whitImg ψ d J T).toSubmodule.subtype) :=
  Submodule.liftQ _ (Submodule.mkQ _ ∘ₗ toImg ψ d J T) fun t ht => by
    refine (Submodule.Quotient.mk_eq_zero _).2 ?_
    exact ⟨t, ht, rfl⟩

theorem stepMap_surjective (ψ : AddChar k Circle) (d : Fin 2 → ℕ)
    (J : Representation ℂ (Levi k fun a => Fin (d a)) Y) (T T' : Subrepresentation J) :
    Function.Surjective (stepMap ψ d J T T') := by
  intro y
  obtain ⟨⟨_, t, ht, rfl⟩, rfl⟩ := Submodule.mkQ_surjective _ y
  exact ⟨Submodule.Quotient.mk ⟨t, ht⟩, rfl⟩

theorem whitKer_subQuot_le (ψ : AddChar k Circle) (d : Fin 2 → ℕ)
    (J : Representation ℂ (Levi k fun a => Fin (d a)) Y) (T T' : Subrepresentation J) :
    whitKer ψ d (subQuot T T') ≤ LinearMap.ker (stepMap ψ d J T T') := by
  refine Submodule.span_le.2 ?_
  rintro w ⟨u, v, rfl⟩
  obtain ⟨t, rfl⟩ := Submodule.mkQ_surjective _ v
  let s : T.toSubmodule := T.toRepresentation (secondEmb d (u : GL (Fin (d 1)) k)) t - ((whitChar ψ (d 1) u : ℂˣ) : ℂ) • t
  have h0 : toImg ψ d J T s = 0 := by
    apply Subtype.ext
    exact (Submodule.Quotient.mk_eq_zero _).2 (Submodule.subset_span ⟨u, (t : Y), rfl⟩)
  show stepMap ψ d J T T' (Submodule.Quotient.mk s) = 0
  show Submodule.mkQ _ (toImg ψ d J T s) = 0
  rw [h0, map_zero]

def coverMap (ψ : AddChar k Circle) (d : Fin 2 → ℕ) (J : Representation ℂ (Levi k fun a => Fin (d a)) Y)
    (T T' : Subrepresentation J) :
    (whit2 ψ d (subQuot T T')).IntertwiningMap (subQuot (whitImg ψ d J T) (whitImg ψ d J T')) :=
  .mk ((whitKer ψ d (subQuot T T')).liftQ (stepMap ψ d J T T') (whitKer_subQuot_le ψ d J T T')) fun g => by
    ext v
    rfl

theorem coverMap_surjective (ψ : AddChar k Circle) (d : Fin 2 → ℕ)
    (J : Representation ℂ (Levi k fun a => Fin (d a)) Y) (T T' : Subrepresentation J) :
    Function.Surjective (coverMap ψ d J T T') := by
  intro y
  obtain ⟨x, rfl⟩ := stepMap_surjective ψ d J T T' y
  exact ⟨Submodule.Quotient.mk x, rfl⟩

theorem iSup_range_of_surjective {G A B C : Type} [Group G] [AddCommGroup A] [Module ℂ A] [AddCommGroup B]
    [Module ℂ B] [AddCommGroup C] [Module ℂ C] {α : Representation ℂ G A} {β : Representation ℂ G B}
    {γ : Representation ℂ G C} (p : β.IntertwiningMap γ) (hp : Function.Surjective p)
    (h : ⨆ f : α.IntertwiningMap β, LinearMap.range f.toLinearMap = ⊤) :
    ⨆ f : α.IntertwiningMap γ, LinearMap.range f.toLinearMap = ⊤ := by
  rw [eq_top_iff]
  have h1 : (⊤ : Submodule ℂ C) = (⊤ : Submodule ℂ B).map p.toLinearMap := by
    rw [Submodule.map_top]
    exact (LinearMap.range_eq_top.2 hp).symm
  rw [h1, ← h, Submodule.map_iSup]
  refine iSup_le fun f => ?_
  refine le_trans ?_ (le_iSup _ (p.comp f))
  rintro _ ⟨_, ⟨v, rfl⟩, rfl⟩
  exact ⟨v, rfl⟩

theorem main : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle) (d : Fin 2 → ℕ) (Y : Type) [AddCommGroup Y] [Module ℂ Y]
    (J : Representation ℂ (Levi k fun a => Fin (d a)) Y) (T T' : Subrepresentation J) (X : Fin 2 → Type)
    [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)] (ρ : ∀ a, Representation ℂ (GL (Fin (d a)) k) (X a)),
    T' ≤ T → (subQuot T T').Equiv (piTensor ρ) →
    ⨆ f : (ρ 0).IntertwiningMap (subQuot (whitImg ψ d J T) (whitImg ψ d J T')), LinearMap.range f.toLinearMap = ⊤ := by
  intro k _ _ _ _ ψ d Y _ _ J T T' X _ _ ρ _ E
  have hE : Function.Surjective (whitMap ψ d E.symm.toIntertwiningMap) := by
    intro y
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ y
    exact ⟨Submodule.Quotient.mk (E x), by
      show Submodule.Quotient.mk (E.symm (E x)) = _
      rw [E.symm_apply_apply]; rfl⟩
  exact iSup_range_of_surjective ((coverMap ψ d J T T').comp (whitMap ψ d E.symm.toIntertwiningMap))
    ((coverMap_surjective ψ d J T T').comp hE) (GlobalTheory.T.whittaker_two_block_intertwiners_span k ψ d X ρ)

end GlobalTheory.CompanionTheory.BZNuPair.WhitCover

end
end

section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.BZPsiPG
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.BZPsiPG.Stab

theorem hRep_fix : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (τ : Representation ℂ (Mir k i) V) (σ : Representation ℂ (GL (Fin t) k) W), IsSmooth τ → IsSmooth σ → ∀ z : V ⊗[ℂ] W, ∃ U ∈ nhds (1 : Mir k (i + t)), ∀ h : HPG k i t, (h : Mir k (i + t)) ∈ U → hRep τ σ h z = z := by
  intro k _ _ _ _ i t V W _ _ _ _ τ σ hτ hσ z
  have hs : IsSmooth (hRep τ σ) :=
    isSmooth_comp (isSmooth_extTensor hτ hσ) _ (GlobalTheory.CompanionTheory.BZPhiPG.Onto.continuous_pgProj k i t)
  obtain ⟨O, hO, e⟩ := isOpen_induced_iff.1 (hs z)
  have hmem : ∀ h : HPG k i t, (h : Mir k (i + t)) ∈ O ↔ hRep τ σ h z = z := fun h =>
    Set.ext_iff.1 e h
  have h1 : (1 : Mir k (i + t)) ∈ O := (hmem 1).2 (by simp)
  exact ⟨O, hO.mem_nhds h1, fun h hh => (hmem h).1 hh⟩

end GlobalTheory.CompanionTheory.BZPsiPG.Stab
end

section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.BZPsiPG
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.BZPsiPG.HpgMem

theorem main : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ)
    (h : HPG k i t), ∃ (x : Fin i → k) (q : Qp k i t),
      (h : Mir k (i + t)) = uM k (i + t) (topV k i t x) * levi k (i + t) (q : GL (Fin (i + t)) k) := by
  intro k _ _ _ _ i t h
  set M : Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k :=
    (((h : GlobalTheory.BZMir.Mir k (i + t)) : GL (Fin (i + t + 1)) k) :
      Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k) with hM
  have hmem : ((h : GlobalTheory.BZMir.Mir k (i + t)) : GL (Fin (i + t + 1)) k) ∈
      GlobalTheory.SmGL.parab k (GlobalTheory.BZMir.Leib.ePG i t) := h.2
  have hp := GlobalTheory.SmGL.mem_parab_iff.1 hmem
  have hp' : ∀ (a : Fin t) (b : Fin (i + 1)),
      M (GlobalTheory.BZMir.Leib.ePG i t ⟨true, a⟩) (GlobalTheory.BZMir.Leib.ePG i t ⟨false, b⟩) = 0 :=
    fun a b => hp true false a b (by decide)
  have hzero : ∀ (r : Fin t) (c : Fin i),
      M (Fin.castSucc (Fin.natAdd i r)) (Fin.castSucc (Fin.castAdd t c)) = 0 := by
    intro r c
    have h₁ : Fin.castSucc (Fin.natAdd i r) = GlobalTheory.BZMir.Leib.ePG i t ⟨true, r⟩ :=
      Fin.ext (by rw [Fin.coe_castSucc, GlobalTheory.CompanionTheory.BZPhiPG.Cells.ePG_true_val, Fin.coe_natAdd])
    have h₂ : Fin.castSucc (Fin.castAdd t c) =
        GlobalTheory.BZMir.Leib.ePG i t ⟨false, Fin.castSucc c⟩ :=
      Fin.ext (by rw [Fin.coe_castSucc, GlobalTheory.CompanionTheory.BZPhiPG.Cells.ePG_false_val, Fin.coe_castAdd])
    rw [h₁, h₂]
    exact hp' r (Fin.castSucc c)
  have hlast : ∀ r : Fin t, M (Fin.castSucc (Fin.natAdd i r)) (Fin.last (i + t)) = 0 := by
    intro r
    have h₁ : Fin.castSucc (Fin.natAdd i r) = GlobalTheory.BZMir.Leib.ePG i t ⟨true, r⟩ :=
      Fin.ext (by rw [Fin.coe_castSucc, GlobalTheory.CompanionTheory.BZPhiPG.Cells.ePG_true_val, Fin.coe_natAdd])
    rw [h₁, ← GlobalTheory.BZMir.Leib.ePG_false_last i t]
    exact hp' r (Fin.last i)
  have hgen : ∀ (r : Fin t) (c : Fin i) (x y : Fin (i + t)), (x : ℕ) = i + r → (y : ℕ) = c →
      ((GlobalTheory.BZMir.mirabolicProjection k (i + t) (h : GlobalTheory.BZMir.Mir k (i + t)) : GL (Fin (i + t)) k) :
        Matrix (Fin (i + t)) (Fin (i + t)) k) x y = 0 := by
    intro r c x y hx hy
    have hx' : x = Fin.natAdd i r := Fin.ext (by rw [hx, Fin.coe_natAdd])
    have hy' : y = Fin.castAdd t c := Fin.ext (by rw [hy, Fin.coe_castAdd])
    subst hx' hy'
    exact hzero r c
  have hq : GlobalTheory.BZMir.mirabolicProjection k (i + t) (h : GlobalTheory.BZMir.Mir k (i + t)) ∈
      GlobalTheory.CompanionTheory.BZPsiPG.Qp k i t := by
    unfold GlobalTheory.CompanionTheory.BZPsiPG.Qp
    rw [GlobalTheory.SmGL.mem_parab_iff]
    intro a b ia jb hab
    cases a <;> cases b
    · exact absurd hab (by decide)
    · exact absurd hab (by decide)
    · refine hgen ia jb _ _ ?_ ?_
      · rfl
      · rfl
    · exact absurd hab (by decide)
  obtain ⟨x, hx⟩ : ∃ x : Fin i → k, x = fun a => M (Fin.castSucc (Fin.castAdd t a)) (Fin.last (i + t)) :=
    ⟨_, rfl⟩
  have hv : (fun r : Fin (i + t) => M (Fin.castSucc r) (Fin.last (i + t))) = GlobalTheory.CompanionTheory.BZPsiPG.topV k i t x := by
    funext r
    cases r using Fin.addCases with
    | left a => rw [GlobalTheory.CompanionTheory.BZPsiPG.topV, Fin.append_left, hx]
    | right b => rw [GlobalTheory.CompanionTheory.BZPsiPG.topV, Fin.append_right, Pi.zero_apply]; exact hlast b
  refine ⟨x, ⟨_, hq⟩, ?_⟩
  apply Subtype.ext
  have hd : ((h : Mir k (i + t)) : GL (Fin (i + t + 1)) k) =
      unip k (i + t) (Multiplicative.ofAdd fun r => M (Fin.castSucc r) (Fin.last (i + t))) *
        glEmb k (i + t) (mirabolicProjection k (i + t) (h : Mir k (i + t))) := by
    have hh := (mem_Mir_iff k ((h : Mir k (i + t)) : GL (Fin (i + t + 1)) k)).1 (h : Mir k (i + t)).2
    ext1
    rw [Units.val_mul]
    show _ = (1 + colMat k (i + t) _) * glEmbMat k (i + t) (blockMat k (i + t) _)
    rw [add_mul, one_mul, colMat_mul_glEmbMat]
    ext a b
    induction a using Fin.lastCases with
    | last =>
      rw [hh]
      induction b using Fin.lastCases <;>
        simp [glEmbMat, colMat, eLast, Fin.castSucc_ne_last, Pi.single_apply]
    | cast a =>
      induction b using Fin.lastCases <;>
        simp [glEmbMat, colMat, blockMat, Fin.castSucc_ne_last, M]
  refine hd.trans ?_
  exact congrArg (· * glEmb k (i + t) (mirabolicProjection k (i + t) (h : Mir k (i + t))))
    (congrArg (fun w => unip k (i + t) (Multiplicative.ofAdd w)) hv)

end GlobalTheory.CompanionTheory.BZPsiPG.HpgMem
end

section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.BZPsiPG
open scoped TensorProduct

theorem _root_.GlobalTheory.T.derivative_of_product_induced_iso : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) (τ : MRep k i) (σ : GRep k t), IsSmooth τ.ρ → IsSmooth σ.ρ → Nonempty ((psiMinus k (prodPGn τ σ).ρ).Equiv (smInd (Qp k i t) (qRep (mtw τ (((t : ℕ) : ℝ) / 2)).ρ (σ.tw (-((i + 1 : ℕ) : ℝ) / 2)).ρ))) → GIso (psiN (prodPGn τ σ)) ((psiN τ).prod σ) := by
  first | exact @GlobalTheory.CompanionTheory.BZPsiPG.Norm.psiN_prodPGn_of_equiv | exact GlobalTheory.CompanionTheory.BZPsiPG.Norm.psiN_prodPGn_of_equiv | (intros; apply GlobalTheory.CompanionTheory.BZPsiPG.Norm.psiN_prodPGn_of_equiv <;> assumption)
end

section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG GlobalTheory.CompanionTheory.BZPhiPG.OntoO Topology
open scoped TensorProduct

noncomputable section
namespace GlobalTheory.CompanionTheory.BZPhiPG.OntoO

theorem muD_toReal_ne_zero : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (t : ℕ) (E C : Set (Fin t → k)) (hE : IsOpen E) (hn : E.Nonempty) (hC : IsCompact C) (hEC : E ⊆ C),
    (muD (k := k) t E).toReal ≠ 0 := by
  intro k _ _ _ _ t E C hE hn hC hEC
  unfold muD
  rw [ENNReal.toReal_ne_zero]
  exact ⟨(hE.measure_pos _ hn).ne',
    ((MeasureTheory.measure_mono hEC).trans_lt hC.measure_lt_top).ne⟩

end GlobalTheory.CompanionTheory.BZPhiPG.OntoO
end
end

section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG
open scoped TensorProduct

theorem _root_.GlobalTheory.T.bump_section_value_local_integral : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) (ψ : AddChar k Circle) (τ : MRep k (i + 1)) (σ : GRep k (t + 1)) (s : kˣ)
    (hψ1 : ∀ y ∈ GlobalTheory.SplitWeil.cball s, ψ y = 1) (w : τ.V ⊗[ℂ] σ.V) (F : XS τ σ)
    (h1 : ∀ d : Fin (t + 1) → k, (∀ j, d j ∈ GlobalTheory.SplitWeil.cball s) → evX F (dEmb k i t d) = w)
    (h0 : ∀ d : Fin (t + 1) → k, (¬ ∀ j, d j ∈ GlobalTheory.SplitWeil.cball s) → evX F (dEmb k i t d) = 0),
  ∃ c : ℂ, c ≠ 0 ∧ intC ψ F 1 = c • w := by
  first | exact @GlobalTheory.CompanionTheory.BZPhiPG.Onto.intC_one_of_bump | exact GlobalTheory.CompanionTheory.BZPhiPG.Onto.intC_one_of_bump | (intros; apply GlobalTheory.CompanionTheory.BZPhiPG.Onto.intC_one_of_bump <;> assumption)
end

section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG
open scoped TensorProduct

theorem _root_.GlobalTheory.T.shifted_embedding_mem_congruence_iff : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (s : kˣ) (hs : ValuativeRel.valuation k (s : k) ≤ 1) (x : Mir k n),
  sEmb k n x ∈ GlobalTheory.CompanionTheory.BZPhiPG.Onto.congM k s hs (n + 1) ↔ x ∈ GlobalTheory.CompanionTheory.BZPhiPG.Onto.congM k s hs n := by
  first | exact @GlobalTheory.CompanionTheory.BZPhiPG.Onto.sEmb_mem_congM_iff | exact GlobalTheory.CompanionTheory.BZPhiPG.Onto.sEmb_mem_congM_iff | (intros; apply GlobalTheory.CompanionTheory.BZPhiPG.Onto.sEmb_mem_congM_iff <;> assumption)
end

section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG
open scoped TensorProduct

theorem _root_.GlobalTheory.T.unipotent_ball_mem_congruence : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) (s : kˣ) (hs : ValuativeRel.valuation k (s : k) ≤ 1) (d : Fin (t + 1) → k),
  ((∀ j, d j ∈ GlobalTheory.SplitWeil.cball s) → dEmb k i t d ∈ GlobalTheory.CompanionTheory.BZPhiPG.Onto.congM k s hs ((i + 1) + t + 1)) ∧
  ∀ (h : Mir k ((i + 1) + t + 1)), h ∈ HPG k (i + 1) (t + 1) → ∀ κ ∈ GlobalTheory.CompanionTheory.BZPhiPG.Onto.congM k s hs ((i + 1) + t + 1),
    dEmb k i t d = h * κ → ∀ j, d j ∈ GlobalTheory.SplitWeil.cball s := by
  first | exact @GlobalTheory.CompanionTheory.BZPhiPG.Onto.dEmb_mem_congM_and_ball | exact GlobalTheory.CompanionTheory.BZPhiPG.Onto.dEmb_mem_congM_and_ball | (intros; apply GlobalTheory.CompanionTheory.BZPhiPG.Onto.dEmb_mem_congM_and_ball <;> assumption)
end

section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG GlobalTheory.CompanionTheory.BZPhiPG.OntoO Topology
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.BZPhiPG.OntoO

theorem piPerm_last_val (i t : ℕ) : ((piPerm i t (Fin.last ((i + 1) + t)) : Fin ((i + 1) + t + 1)) : ℕ) = i := by
  have key : ∀ x : Fin (i + (t + 1) + 1), (x : ℕ) = i + 1 + t →
      ((GlobalTheory.BZMir.Leib.eGP (i + 1) t ((GlobalTheory.BZMir.Leib.ePG i (t + 1)).symm x) :
        Fin ((i + 1) + t + 1)) : ℕ) = i := by
    intro x hx
    have hxl : x = Fin.last (i + (t + 1)) := Fin.ext (by rw [Fin.val_last]; omega)
    subst hxl
    have h2 : (GlobalTheory.BZMir.Leib.ePG i (t + 1)).symm (Fin.last (i + (t + 1))) =
        ⟨false, Fin.last i⟩ := by
      rw [Equiv.symm_apply_eq, GlobalTheory.BZMir.Leib.ePG_false_last]
    rw [h2]
    exact GlobalTheory.CompanionTheory.LeibPhi.blockIndex_false_val (i + 1) t (Fin.last i)
  first
    | (simp only [GlobalTheory.CompanionTheory.BZPhiPG.piPerm, Equiv.trans_apply]; exact key _ rfl)
    | exact key _ rfl

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem wEl_inv_entry (i t : ℕ) (c : Fin ((i + 1) + t + 1)) (hc : (c : ℕ) = i) :
    ((((wEl k i t)⁻¹ : Mir k ((i + 1) + t + 1)) : GL (Fin ((i + 1) + t + 2)) k) :
      Matrix (Fin ((i + 1) + t + 2)) (Fin ((i + 1) + t + 2)) k)
      (Fin.castSucc (Fin.last ((i + 1) + t))) (Fin.castSucc c) = 1 := by
  have hσ : GlobalTheory.CompanionTheory.BZPhiPG.piPerm i t (Fin.last ((i + 1) + t)) = c :=
    Fin.ext ((GlobalTheory.CompanionTheory.BZPhiPG.OntoO.piPerm_last_val i t).trans hc.symm)
  rw [GlobalTheory.CompanionTheory.BZPhiPG.wEl, ← map_inv]
  change GlobalTheory.BZMir.glEmbMat k ((i + 1) + t + 1)
      (((GlobalTheory.CompanionTheory.BZPhiPG.wGL k i t)⁻¹ : GL (Fin ((i + 1) + t + 1)) k) :
        Matrix (Fin ((i + 1) + t + 1)) (Fin ((i + 1) + t + 1)) k)
      (Fin.castSucc (Fin.last ((i + 1) + t))) (Fin.castSucc c) = 1
  simp only [GlobalTheory.BZMir.glEmbMat, Fin.lastCases_castSucc]
  change Equiv.Perm.permMatrix k (GlobalTheory.CompanionTheory.BZPhiPG.piPerm i t) (Fin.last ((i + 1) + t)) c = 1
  simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, hσ]

theorem dEmb_zero (i t : ℕ) : dEmb k i t 0 = 1 := by
  have h : Fin.append (0 : Fin (i + 1) → k) (0 : Fin (t + 1) → k) = 0 := by
    funext j
    refine Fin.addCases (fun a => ?_) (fun b => ?_) j
    · rw [Fin.append_left]; rfl
    · rw [Fin.append_right]; rfl
  apply Subtype.ext
  change GlobalTheory.BZMir.unip k ((i + 1) + (t + 1))
      (Multiplicative.ofAdd (Fin.append (0 : Fin (i + 1) → k) (0 : Fin (t + 1) → k))) = 1
  rw [h, ofAdd_zero, map_one]

theorem wEl_notMem_Cl (i t : ℕ) : wEl k i t ∉ Cl k i t := by
  intro hmem
  simp only [GlobalTheory.CompanionTheory.BZPhiPG.Cl, Set.mem_setOf_eq] at hmem
  have h := hmem (Fin.last i)
  have hc : (Fin.castLE (by omega) (Fin.last i) : Fin ((i + 1) + t + 1 + 1)) =
      Fin.castSucc (⟨i, by omega⟩ : Fin ((i + 1) + t + 1)) := Fin.ext rfl
  rw [hc, GlobalTheory.CompanionTheory.BZPhiPG.OntoO.wEl_inv_entry k i t ⟨i, by omega⟩ rfl] at h
  exact one_ne_zero h

theorem wEl_notMem_Cl_and_dEmb_zero : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (i t : ℕ), wEl k i t ∉ Cl k i t ∧ dEmb k i t 0 = 1 := by
  intro k _ _ _ _ i t
  exact ⟨GlobalTheory.CompanionTheory.BZPhiPG.OntoO.wEl_notMem_Cl k i t, GlobalTheory.CompanionTheory.BZPhiPG.OntoO.dEmb_zero k i t⟩

end GlobalTheory.CompanionTheory.BZPhiPG.OntoO
end
end
