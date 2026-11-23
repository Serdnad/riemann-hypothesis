module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsUnitarySupportedAtPlaceOfMulEqIdem
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle163
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle295
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PlacesToAdeles
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle029
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle345
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
import Mathlib.Tactic.Linter.Style
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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.JointSmooth
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiStarOfMid
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle019
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.UnitRatio
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle076

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl

noncomputable section

namespace GlobalTheory.SplitLat

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def place (q : SplitPt D k) : GlobalTheory.LocMod.Place D k where
  e := q.e
  split := q.split
  π := q.pr
  ι := q.sec
  π_ι := q.pr_sec
  ι_π := q.sec_pr
  cont_π := q.cont_pr
  cont_ι := q.cont_sec

theorem suppAt_one (e : AE D) (S : HSp D) : SuppAt e S 1 := by
  intro i j
  simp [Formalism.L2.Theta.mt]

theorem isLoc_one (q : SplitPt D k) {S : HSp D} {Y : Type} [Fintype Y] [DecidableEq Y]
    (F : GlobalTheory.LocMod.Frame k S.rank Y) : (place q).IsLoc F 1 1 := by
  refine ⟨suppAt_one _ _, ?_⟩
  simp [Formalism.L2.Theta.mt, F.βγ, place]

theorem locGrp (q : SplitPt D k) (S : HSp D) (Y : Type) [Fintype Y] [DecidableEq Y]
    (F : GlobalTheory.LocMod.Frame k S.rank Y) :
    (∀ gk : GL Y k, ∃! g, (place q).IsLoc F g gk) ∧ (∀ g, SuppAt (place q).e S g → ∃ gk, (place q).IsLoc F g gk) ∧
      ∀ g gk h hk, (place q).IsLoc F g gk → (place q).IsLoc F h hk → (place q).IsLoc F (g * h) (gk * hk) :=
  (GlobalTheory.T.splitPlace_localGroupElements_jacobi_bessel D k (place q)).1 S Y F

def frameOf (q : SplitPt D k) (S : HSp D) (Y : Type) [Fintype Y] [DecidableEq Y]
    (F : GlobalTheory.LocMod.Frame k S.rank Y) : Frame q S Y where
  b := F.β
  b' := F.γ
  bb' := F.βγ
  b'b := F.γβ
  gl :=
    { toFun := fun g => ((locGrp q S Y F).1 g).exists.choose
      map_one' := ((locGrp q S Y F).1 1).unique ((locGrp q S Y F).1 1).exists.choose_spec (isLoc_one q F)
      map_mul' := fun g g' => ((locGrp q S Y F).1 (g * g')).unique ((locGrp q S Y F).1 (g * g')).exists.choose_spec
        ((locGrp q S Y F).2.2 _ _ _ _ ((locGrp q S Y F).1 g).exists.choose_spec
          ((locGrp q S Y F).1 g').exists.choose_spec) }
  gl_supp g := ((locGrp q S Y F).1 g).exists.choose_spec.1
  gl_mat g := ((locGrp q S Y F).1 g).exists.choose_spec.2

def stdLat (k : Type) [Field k] [ValuativeRel k] (Y : Type) : Submodule 𝒪[k] (Y → k) :=
  Submodule.pi Set.univ fun _ => (1 : Submodule 𝒪[k] k)

theorem mem_std {Y : Type} (y : Y → k) : y ∈ stdLat k Y ↔ ∀ i, y i ∈ 𝒪[k] := by
  simp only [stdLat, Submodule.mem_pi, Set.mem_univ, true_implies, Submodule.mem_one]
  exact forall_congr' fun i => ⟨fun ⟨c, hc⟩ => hc ▸ c.2, fun h => ⟨⟨y i, h⟩, rfl⟩⟩

theorem std_eq_span (Y : Type) [Fintype Y] [DecidableEq Y] :
    stdLat k Y = Submodule.span 𝒪[k] (Set.range fun i : Y => (Pi.single i 1 : Y → k)) := by
  apply le_antisymm
  · intro x hx
    have hx' := (mem_std x).1 hx
    have : x = ∑ i, (⟨x i, hx' i⟩ : 𝒪[k]) • (Pi.single i 1 : Y → k) := by
      funext j
      simp [Finset.sum_apply, Pi.single_apply, Subring.smul_def, smul_eq_mul]
    rw [this]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  · rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    refine (mem_std _).2 fun i => ?_
    show (Pi.single j (1 : k) : Y → k) i ∈ 𝒪[k]
    rw [Pi.single_apply]
    split_ifs
    · exact one_mem _
    · exact zero_mem _

theorem isLattice_std (Y : Type) [Fintype Y] [DecidableEq Y] : Submodule.IsFullLattice k (stdLat k Y) := by
  refine { toIsLattice := ?_, span_eq_top := ?_ }
  · apply Submodule.IsLattice.of_fg k
    rw [std_eq_span]
    exact Submodule.fg_span (Set.finite_range _)
  · apply eq_top_iff.mpr
    rw [← (Pi.basisFun k Y).span_eq, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    apply Submodule.subset_span
    refine (mem_std _).2 fun j => ?_
    rw [Pi.basisFun_apply, Pi.single_apply]
    split_ifs
    · exact one_mem _
    · exact zero_mem _

theorem idAt_mono {P Q : Pl D → Prop} (hPQ : ∀ w, P w → Q w) : idAt D P ≤ idAt D Q := by
  intro a ha
  obtain ⟨h1, h2⟩ := Submodule.mem_inf.1 ha
  refine Submodule.mem_inf.2 ⟨h1, (Submodule.mem_iInf _).2 fun w => ?_⟩
  exact (Submodule.mem_iInf _).1 h2 ⟨w.1, fun hw => w.2 (hPQ _ hw)⟩

theorem latV_le_of_off {S : HSp D} {L L' : Lat S} (hL : Submodule.IsLattice D.host.E L)
    (hL' : Submodule.IsLattice D.host.E L') {v₀ v : Pl D} (hv : v ≠ v₀)
    (h : latV S L (· ≠ v₀) = latV S L' (· ≠ v₀)) : latV S L (· = v) ≤ latV S L' (· = v) := by
  intro y hy
  obtain ⟨⟨ε, -, -, hεint, hεat, -⟩, hSv⟩ := GlobalTheory.T.adelicPoint_components_atPlaces_lattices_vacua D (· = v)
  have hyv := ((hSv S).2.2.2 L y hL).1 hy
  have hoff := ((GlobalTheory.T.adelicPoint_components_atPlaces_lattices_vacua D (· ≠ v₀)).2 S).2.2.2
  have hy₀ : y ∈ latV S L (· ≠ v₀) := by
    rw [hoff L y hL]
    refine ⟨fun i => idAt_mono (fun w hw => hw ▸ hv) (hyv.1 i), fun u _ e he => ?_⟩
    by_cases huv : u = v
    · subst huv
      exact hyv.2 u rfl e he
    · obtain ⟨⟨εu, -, -, -, hεuat, hεuoff⟩, -⟩ := GlobalTheory.T.adelicPoint_components_atPlaces_lattices_vacua D (· = u)
      have hz : e • y = 0 := by
        funext i
        have hyi : y i ∈ idOff D (· = u) :=
          (Submodule.mem_iInf _).2 fun w =>
            (Submodule.mem_iInf _).1 (Submodule.mem_inf.1 (hyv.1 i)).2 ⟨w.1, fun hw => huv (w.2.symm.trans hw)⟩
        change e * y i = 0
        rw [← (hεuat e).1 he.1, mul_comm εu e, mul_assoc, (hεuoff (y i)).1 hyi, mul_zero]
      rw [hz]
      exact zero_mem _
  rw [h] at hy₀
  have h2 := ((hoff L' y hL').1 hy₀).2 v hv ε hεint
  have hεy : ε • y = y := funext fun i => (hεat (y i)).1 (hyv.1 i)
  rwa [hεy] at h2

theorem exists_selfDual_frame : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : SplitPt D k) (S : HSp D) (Y : Type) [Fintype Y] [DecidableEq Y] (F : GlobalTheory.LocMod.Frame k S.rank Y) (L₀ : Lat S), IsSelfDualC S L₀ → ∃ L : Lat S, IsSelfDualC S L ∧ (∀ v, v ≠ q.v → latV S L (· = v) = latV S L₀ (· = v)) ∧ ∀ y : Y → k, (∀ i, y i ∈ 𝒪[k]) ↔ (fun i => q.sec ((F.β *ᵥ y) i)) ∈ latV S L (· = q.v) := by
  intro D k _ _ _ _ q S Y _ _ F L₀ hL₀
  obtain ⟨M, hM, hMΛ, hoff⟩ :=
    GlobalTheory.T.exists_selfDual_lattice_with_prescribed_splitComponent D k q S Y (frameOf q S Y F) L₀ (stdLat k Y) hL₀ (isLattice_std Y)
  refine ⟨M, hM, fun v hv => le_antisymm (latV_le_of_off hM.1 hL₀.1 hv hoff)
    (latV_le_of_off hL₀.1 hM.1 hv hoff.symm), fun y => ?_⟩
  exact (mem_std y).symm.trans (hMΛ y)

end GlobalTheory.SplitLat
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.RootEx GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.SplitWeil GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.JacFramePair

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem pair_col (p : Place D k) {N ρ : ℕ} {κ : Type} [Fintype κ] (G : Matrix (Fin N) (Fin N) D.host.E)
    (X : Matrix (Fin N) κ D.host.E) (e : Matrix (Fin N) (Fin ρ) D.host.E) (j : κ) (i : Fin ρ) :
    ∑ r, p.pr (X r j) * p.pr (star ((G *ᵥ fun r => e r i) r)) = p.pr (star ((Xᴴ * G * e) j i)) := by
  have h : star ((Xᴴ * G * e) j i) = ∑ r, X r j * star ((G *ᵥ fun r => e r i) r) := by
    rw [Matrix.mul_assoc, Matrix.mul_apply, star_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    have hv : (G * e) r i = (G *ᵥ fun r => e r i) r := by simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]
    rw [star_mul', Matrix.conjTranspose_apply, star_star, hv, mul_comm]
  rw [h]
  change _ = Witness.prH p _

  rw [map_sum]
  exact Finset.sum_congr rfl fun r _ => (map_mul (Witness.prH p) _ _).symm

theorem pair_scaled (p : Place D k) {N ρ : ℕ} {κ Z : Type} [Fintype κ] (G : Matrix (Fin N) (Fin N) D.host.E)
    (X : Matrix (Fin N) κ D.host.E) (e : Matrix (Fin N) (Fin ρ) D.host.E) (β : Matrix (Fin N) Z k) (m : Z) (j : κ)
    (t : k) (h : ∀ r, β r m = t * p.pr (X r j)) (i : Fin ρ) :
    ∑ r, β r m * p.pr (star ((G *ᵥ fun r => e r i) r)) = t * p.pr (star ((Xᴴ * G * e) j i)) := by
  simp_rw [h, mul_assoc, ← Finset.mul_sum, pair_col]

theorem pr_zero (p : Place D k) : p.pr 0 = 0 := map_zero (Witness.prH p)

theorem pr_one (p : Place D k) : p.pr 1 = 1 := map_one (Witness.prH p)

theorem pr_star_one (p : Place D k) {ρ : ℕ} (i' i : Fin ρ) :
    p.pr (star ((1 : Matrix (Fin ρ) (Fin ρ) D.host.E) i' i)) = if i' = i then 1 else 0 := by
  rw [Matrix.one_apply]
  split_ifs <;> simp [pr_zero, pr_one]

theorem isJacFrame_pairing : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : Place D k) (ρ : ℕ) (J : JacLev D ρ) (s hh : k) (n : Type) [Fintype n] [DecidableEq n] (c : ℕ)
    (F₀ : Frame k J.W₀.rank n) (F : Frame k J.W.rank (n ⊕ Fin c)),
    p.IsJacFrame J s hh F₀ F → valuation k s = 1 → valuation k hh = 1 → valuation k p.xi = 1 → ∀ i : Fin ρ,
    ∃ (b : k) (m₀ : n ⊕ Fin c), valuation k b = 1 ∧ (∀ r, b * p.pr (J.d.e r i) = F.β r m₀) ∧
      (∀ m, ∑ r, F.β r m * p.pr (star ((J.W.gram *ᵥ fun r => J.d.e r i) r)) ∈ 𝒪[k]) ∧
      ∃ m, valuation k (∑ r, F.β r m * p.pr (star ((J.W.gram *ᵥ fun r => J.d.e r i) r))) = 1 := by
  intro D k _ _ _ _ p ρ J s hh n _ _ c F₀ F hJ hs hhh hx i
  obtain ⟨hc, h1, h2, h3⟩ := hJ
  subst hc
  have vt : ∀ l : ℕ, valuation k (s * (hh / p.xi) * (-1 / p.xi) ^ l) = 1 := fun l => by
    simp [map_mul, map_div₀, map_pow, Valuation.map_neg, hs, hhh, hx]
  have inrLo : ∀ (j : Fin (2 * ρ)) (hj : j.val < ρ),
      ∑ r, F.β r (Sum.inr j) * p.pr (star ((J.W.gram *ᵥ fun r => J.d.e r i) r)) = 0 := fun j hj => by
    rw [pair_scaled p J.W.gram J.d.e J.d.e F.β (Sum.inr j) (⟨j.val, hj⟩ : Fin ρ) _ (h2 ⟨j.val, hj⟩ j rfl), J.d.ee]
    simp [pr_zero]
  have inrHi : ∀ (j : Fin (2 * ρ)) (hj : ρ ≤ j.val),
      ∑ r, F.β r (Sum.inr j) * p.pr (star ((J.W.gram *ᵥ fun r => J.d.e r i) r)) =
        s * (hh / p.xi) * (-1 / p.xi) ^ (ρ - 1 - (2 * ρ - 1 - j.val)) *
          (if (⟨2 * ρ - 1 - j.val, by omega⟩ : Fin ρ) = i then 1 else 0) := fun j hj => by
    rw [pair_scaled p J.W.gram J.d.e' J.d.e F.β (Sum.inr j) (⟨2 * ρ - 1 - j.val, by omega⟩ : Fin ρ) _
      (h3 ⟨2 * ρ - 1 - j.val, by omega⟩ j (by simp only; omega)), J.d.e'e, pr_star_one]
  refine ⟨s * p.xi ^ (ρ - i.val), Sum.inr ⟨i.val, by omega⟩, by simp [map_mul, map_pow, hs, hx],
    fun r => (h2 i _ rfl r).symm, ?_, Sum.inr ⟨2 * ρ - 1 - i.val, by omega⟩, ?_⟩
  · rintro (a | j)
    · have e0 : ∑ r, F.β r (Sum.inl a) * p.pr (star ((J.W.gram *ᵥ fun r => J.d.e r i) r)) = 0 := by
        simp_rw [h1, Matrix.mul_apply, Matrix.map_apply, Finset.sum_mul]
        rw [Finset.sum_comm]
        refine Finset.sum_eq_zero fun b _ => ?_
        have := pair_col p J.W.gram J.d.i₀ J.d.e b i
        rw [J.d.i₀e, Matrix.zero_apply, star_zero, pr_zero] at this
        calc ∑ r, p.pr (J.d.i₀ r b) * F₀.β b a * p.pr (star ((J.W.gram *ᵥ fun r => J.d.e r i) r))
            = F₀.β b a * ∑ r, p.pr (J.d.i₀ r b) * p.pr (star ((J.W.gram *ᵥ fun r => J.d.e r i) r)) := by
              rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun r _ => by ring
          _ = 0 := by rw [this, mul_zero]
      rw [e0]
      exact zero_mem _
    · by_cases hj : j.val < ρ
      · rw [inrLo j hj]
        exact zero_mem _
      · rw [inrHi j (by omega), Valuation.mem_integer_iff, map_mul, vt, one_mul]
        split_ifs <;> simp
  · rw [inrHi _ (by simp only; omega), map_mul, vt, one_mul, if_pos (Fin.ext (by simp only; omega)), map_one]

end GlobalTheory.JacFramePair
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.RootEx GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.SplitWeil GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.BesPair

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  (p : Place D k)

theorem sum_pr_star {N : ℕ} (x y : Fin N → D.host.E) :
    ∑ r, p.pr (x r) * p.pr (star (y r)) = p.pr (star (star x ⬝ᵥ y)) := by
  change ∑ r, Witness.prH p (x r) * Witness.prH p (star (y r)) = Witness.prH p (star (star x ⬝ᵥ y))

  rw [dotProduct, star_sum, map_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [Pi.star_apply, star_mul, star_star, map_mul]
  ring

theorem col_pair {N : ℕ} {ι τ : Type} [Fintype ι] (X : Matrix (Fin N) ι D.host.E)
    (G : Matrix (Fin N) (Fin N) D.host.E) (e : Matrix (Fin N) τ D.host.E) (j : ι) (i : τ) :
    star (fun r => X r j) ⬝ᵥ (G *ᵥ fun r => e r i) = (Xᴴ * G * e) j i := by
  rw [Matrix.mul_assoc, Matrix.mul_apply]
  rfl

theorem mulVec_col {N M : ℕ} {τ : Type} (A : Matrix (Fin M) (Fin N) D.host.E) (e : Matrix (Fin N) τ D.host.E) (i : τ) :
    (A *ᵥ fun r => e r i) = fun u => (A * e) u i := by
  funext u
  rfl

theorem pr_zero : p.pr (0 : D.host.E) = 0 := (Witness.prH p).map_zero

theorem pr_one : p.pr (1 : D.host.E) = 1 := (Witness.prH p).map_one

theorem bes_cols : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : Place D k) (ρ : ℕ) (B : BesLev D ρ) (s : k) (n : Type) [Fintype n] [DecidableEq n] (c : ℕ)
    (FA : Frame k B.A.rank n) (F : Frame k B.V.rank (n ⊕ Fin c)),
    p.IsBesFrame B s FA F → valuation k s = 1 → valuation k (p.hz B) = 1 → valuation k p.xi = 1 → ∀ i : Fin ρ,
    ∃ (b : k) (m₀ : n ⊕ Fin c), valuation k b = 1 ∧ (∀ r, b * p.pr (B.d.e r i) = F.β r m₀) ∧
      (∀ m, ∑ r, F.β r m * p.pr (star ((B.V.gram *ᵥ fun r => B.d.e r i) r)) ∈ 𝒪[k]) ∧
      ∃ m, valuation k (∑ r, F.β r m * p.pr (star ((B.V.gram *ᵥ fun r => B.d.e r i) r))) = 1 := by
  intro D k _ _ _ _ p ρ B s n _ _ c FA F h hs hz hx i
  obtain ⟨rfl, h1, h2, h3, h4⟩ := h
  have hC : ∀ t : ℕ, valuation k (s * (-p.hz B / p.xi) * (-1 / p.xi) ^ t) = 1 := by
    intro t
    simp [map_mul, map_div₀, Valuation.map_neg, map_pow, hs, hz, hx]

  have hval : ∀ (i' : Fin ρ) (j : Fin (2 * ρ + 1)), j.val + i'.val = 2 * ρ →
      ∑ r, F.β r (Sum.inr j) * p.pr (star ((B.V.gram *ᵥ fun r => B.d.e r i) r)) =
        s * (-p.hz B / p.xi) * (-1 / p.xi) ^ (ρ - 1 - i'.val) * p.pr (star ((1 : Matrix (Fin ρ) (Fin ρ) D.host.E) i' i)) := by
    intro i' j hj
    simp_rw [h4 i' j hj, mul_assoc, ← Finset.mul_sum]
    rw [sum_pr_star, col_pair, B.d.e'e]
  have hq : ∀ m, (∑ r, F.β r m * p.pr (star ((B.V.gram *ᵥ fun r => B.d.e r i) r))) = 0 ∨
      valuation k (∑ r, F.β r m * p.pr (star ((B.V.gram *ᵥ fun r => B.d.e r i) r))) = 1 := by
    rintro (a | ⟨j, hj⟩)
    · left
      have hM : (B.d.i₀ * B.o.iA)ᴴ * B.V.gram * B.d.e = 0 := by
        rw [Matrix.conjTranspose_mul,
          show B.o.iAᴴ * B.d.i₀ᴴ * B.V.gram * B.d.e = B.o.iAᴴ * (B.d.i₀ᴴ * B.V.gram * B.d.e) by
            simp only [Matrix.mul_assoc],
          B.d.i₀e, Matrix.mul_zero]
      simp_rw [h1, Matrix.mul_apply, Matrix.map_apply, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_eq_zero fun u _ => ?_
      calc ∑ r, p.pr ((B.d.i₀ * B.o.iA) r u) * FA.β u a * p.pr (star ((B.V.gram *ᵥ fun r => B.d.e r i) r))
          = (∑ r, p.pr ((B.d.i₀ * B.o.iA) r u) * p.pr (star ((B.V.gram *ᵥ fun r => B.d.e r i) r))) * FA.β u a := by
            rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun _ _ => by ring
        _ = 0 := by
            rw [sum_pr_star p (fun r => (B.d.i₀ * B.o.iA) r u), col_pair, hM, Matrix.zero_apply, star_zero, pr_zero,
              zero_mul]
    · rcases lt_trichotomy j ρ with hlt | heq | hgt
      · left
        simp_rw [h2 ⟨j, hlt⟩ ⟨j, hj⟩ rfl, mul_assoc, ← Finset.mul_sum]
        rw [sum_pr_star, col_pair, B.d.ee, Matrix.zero_apply, star_zero, pr_zero, mul_zero, mul_zero]
      · left
        simp_rw [h3 ⟨j, hj⟩ heq, mul_assoc, ← Finset.mul_sum]
        rw [sum_pr_star, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, mulVec_col, B.d.i₀e]
        simp only [Matrix.zero_apply]
        rw [dotProduct_zero', star_zero, pr_zero, mul_zero]
      · have hi' : 2 * ρ - j < ρ := by omega
        rw [hval ⟨2 * ρ - j, hi'⟩ ⟨j, hj⟩ (by simp only; omega)]
        by_cases he : (⟨2 * ρ - j, hi'⟩ : Fin ρ) = i
        · right
          rw [he, Matrix.one_apply_eq, star_one, pr_one, mul_one]
          exact hC _
        · left
          rw [Matrix.one_apply_ne he, star_zero, pr_zero, mul_zero]
  refine ⟨s * p.xi ^ (ρ - i.val), Sum.inr ⟨i.val, by omega⟩, ?_, fun r => (h2 i _ rfl r).symm, fun m => ?_, ?_⟩
  · simp [map_mul, map_pow, hs, hx]
  · rw [Valuation.mem_integer_iff]
    rcases hq m with h0 | h0
    · rw [h0, map_zero]; exact zero_le'
    · exact h0.le
  · refine ⟨Sum.inr ⟨2 * ρ - i.val, by omega⟩, ?_⟩
    rw [hval i _ (by simp only; omega), Matrix.one_apply_eq, star_one, pr_one, mul_one]
    exact hC _

end GlobalTheory.BesPair
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl GlobalTheory.Fam ValuativeRel IsLocalRing
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.LevIdx

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {Y : Type} [Fintype Y] [DecidableEq Y]

theorem mt_mul (S : HSp D) (g h : GA D S) : mt S (g * h) = mt S g * mt S h := by
  simp [Formalism.L2.Theta.mt]

theorem mt_one (S : HSp D) : mt S 1 = 1 := by
  simp [Formalism.L2.Theta.mt]

def locHom (q : SplitPt D k) (S : HSp D) (F : GlobalTheory.LocMod.Frame k S.rank Y) : GA D S →* GL Y k where
  toFun g := ⟨F.γ * (mt S g).map q.pr * F.β, F.γ * (mt S g⁻¹).map q.pr * F.β, by
      rw [show F.γ * (mt S g).map q.pr * F.β * (F.γ * (mt S g⁻¹).map q.pr * F.β) =
        F.γ * ((mt S g).map q.pr * (F.β * F.γ) * (mt S g⁻¹).map q.pr) * F.β by simp only [Matrix.mul_assoc],
        F.βγ, Matrix.mul_one, ← Matrix.map_mul, ← mt_mul, mul_inv_cancel, mt_one, Matrix.map_one _ (map_zero _) (map_one _),
        Matrix.mul_one, F.γβ], by
      rw [show F.γ * (mt S g⁻¹).map q.pr * F.β * (F.γ * (mt S g).map q.pr * F.β) =
        F.γ * ((mt S g⁻¹).map q.pr * (F.β * F.γ) * (mt S g).map q.pr) * F.β by simp only [Matrix.mul_assoc],
        F.βγ, Matrix.mul_one, ← Matrix.map_mul, ← mt_mul, inv_mul_cancel, mt_one, Matrix.map_one _ (map_zero _) (map_one _),
        Matrix.mul_one, F.γβ]⟩
  map_one' := by
    ext1; simp only [mt_one, Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one, F.γβ]; rfl
  map_mul' g h := by
    ext1
    change F.γ * (mt S (g * h)).map q.pr * F.β = F.γ * (mt S g).map q.pr * F.β * (F.γ * (mt S h).map q.pr * F.β)
    rw [mt_mul, Matrix.map_mul]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc F.β F.γ, F.βγ, Matrix.one_mul]

theorem locHom_val (q : SplitPt D k) (S : HSp D) (F : GlobalTheory.LocMod.Frame k S.rank Y) (g : GA D S) :
    (locHom q S F g).val = F.γ * (mt S g).map q.pr * F.β := rfl

theorem eq_locHom_iff (q : SplitPt D k) (S : HSp D) (F : GlobalTheory.LocMod.Frame k S.rank Y) (g : GA D S) (x : GL Y k) :
    (mt S g).map q.pr = F.β * x.val * F.γ ↔ x = locHom q S F g := by
  constructor
  · intro h
    ext1
    rw [locHom_val, h]
    simp only [Matrix.mul_assoc, F.γβ, Matrix.mul_one]
    rw [← Matrix.mul_assoc, F.γβ, Matrix.one_mul]
  · rintro rfl
    rw [locHom_val]
    simp only [← Matrix.mul_assoc, F.βγ, Matrix.one_mul]
    rw [Matrix.mul_assoc, F.βγ, Matrix.mul_one]

theorem continuous_locHom (q : SplitPt D k) (S : HSp D) (F : GlobalTheory.LocMod.Frame k S.rank Y) :
    Continuous (locHom q S F) := by
  rw [Units.continuous_iff]
  have hm : Continuous fun g : GA D S => (mt S g).map q.pr :=
    (GlobalTheory.MixModel.continuous_mt S).matrix_map q.cont_pr
  refine ⟨(continuous_const.matrix_mul hm).matrix_mul continuous_const, ?_⟩
  have hi : Continuous fun g : GA D S => (mt S g⁻¹).map q.pr :=
    ((GlobalTheory.MixModel.continuous_mt S).comp continuous_inv).matrix_map q.cont_pr
  exact (continuous_const.matrix_mul hi).matrix_mul continuous_const

theorem vol_mul_relIndex {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G]
    [BorelSpace G] (μ : Measure G) [μ.IsMulLeftInvariant] (H H' : Subgroup G) (hle : H' ≤ H)
    (hc : IsCompact (H : Set G)) (ho : IsOpen (H' : Set G)) : μ.real H' * (H'.relIndex H : ℝ) = μ.real H := by
  haveI : CompactSpace H := isCompact_iff_compactSpace.1 hc
  have hHo : IsOpen (H : Set G) := Subgroup.isOpen_mono hle ho
  have ho' : IsOpen ((H'.subgroupOf H : Subgroup H) : Set H) := ho.preimage continuous_subtype_val
  haveI : Finite (H ⧸ H'.subgroupOf H) := (H'.subgroupOf H).quotient_finite_of_isOpen ho'
  haveI : (H'.subgroupOf H).FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  have hemb : MeasurableEmbedding (H.subtype : H → G) := MeasurableEmbedding.subtype_coe hHo.measurableSet
  have : (μ.comap (H.subtype : H → G)).IsMulLeftInvariant := Measure.IsMulLeftInvariant.comap μ hemb
  have key := (H'.subgroupOf H).index_mul_measure ho'.measurableSet (μ.comap (H.subtype : H → G))
  rw [hemb.comap_apply, hemb.comap_apply] at key
  have e1 : (H.subtype : H → G) '' Set.univ = (H : Set G) := by ext x; simp
  have e2 : (H.subtype : H → G) '' ((H'.subgroupOf H : Subgroup H) : Set H) = (H' : Set G) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨⟨x, hle hx⟩, hx, rfl⟩
  rw [e1, e2] at key
  rw [Subgroup.relIndex, Measure.real, Measure.real, ← key, ENNReal.toReal_mul, mul_comm]
  simp

end GlobalTheory.LevIdx
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.LocMod

namespace GlobalTheory.LocModTheta

theorem flat_model_theta : ∀ (D : D7), FlatLaw D → GlobalTheory.FinPl.FlatLaws D → OmLoc D → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (p : Place D k) (ν : Measure k), ν.IsAddHaarMeasure → ∀ (ψ : AddChar (AF D.host.F) ℂ) (ψk : AddChar k Circle), p.IsChar ψ ψk → ∀ (ρ : ℕ) (B : BesLev D ρ) (J : JacLev D ρ) (st : StepBF ψ B J) (s : k), s ≠ 0 → ∀ (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c : ℕ) (FA : Frame k B.A.rank n') (F₀ : Frame k B.V₀.rank (n' ⊕ Unit)) (FV : Frame k B.V.rank (n' ⊕ Fin (c + 1))) (G₀ : Frame k J.W₀.rank n) (FW : Frame k J.W.rank (n ⊕ Fin c)), p.IsCoreFrame B s FA F₀ → p.IsBesFrame B s FA FV → p.IsJacFrame J s (p.hz B) G₀ FW → ∀ (Tm : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) →ₗ[ℂ] (WO B.V J.W → ℂ)), p.IsModel ψ FV FW Tm → ∀ (L₀ : SB (Matrix n (n' ⊕ Unit) k) →ₗ[ℂ] (WO B.V₀ J.W₀ → ℂ)), (∀ (Φ : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)) (Ψ : SB (Matrix n (n' ⊕ Unit) k)), Ψ.1 = GlobalTheory.LocFlat.flCol ψk ν (ρ + 1) Φ.1 → flatBF st (Tm Φ) = L₀ Ψ) → ∀ Ψ, IsThetaFunO ψ B.V₀ J.W₀ (L₀ Ψ) := by
  intro D _hFL hFlat _hOm k _ _ _ _ _ _ p ν hν ψ ψk hchar ρ B J st s _hs n n' _ _ _ _ c FA F₀ FV G₀ FW _hCore hBes _hJac Tm hTm L₀ hL Ψ
  have hstd : IsStdChar D ψ (-1) := st.weil.std
  have hcont : Continuous ψk := ((GlobalTheory.T.weilCharacter_splitPlace_exists_continuous_nontrivial D k p ψ hstd).2.1 ψk hchar).1
  have hc : c = 2 * ρ := by have := hBes.1; omega
  obtain ⟨Φ₀, hΦ₀, hfl⟩ := ((GlobalTheory.T.flatMaps_preserve_schwartzBruhat_and_surjective k ψk ν hcont hν n n' c (ρ + 1) (by omega)).1 (by omega)).2 Ψ.1 Ψ.2
  rw [← hL ⟨Φ₀, hΦ₀⟩ Ψ hfl.symm]
  exact ((hFlat ψ (fun _ => True)).1 ρ B J st).Heisenberg₂.theta (Tm ⟨Φ₀, hΦ₀⟩) (hTm.theta _)

end GlobalTheory.LocModTheta
end
