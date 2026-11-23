module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle022
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle258
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle166
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle335
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle287
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle192
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle146
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle174
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle164
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle163
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PlacewiseToAdelicDecompositionForall
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualSplitComponentIsLatticeStabilizerEq
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceLocalGroupElementsJacobiBessel
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainStepFockVectorSphericalOffS
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsUnitarySupportedAtPlaceOfMulEqIdem
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle011
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle342
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PlacesToAdeles
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselFlatMapLocalUnipotentTranslationLaw
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiStarOfMid
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle019
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.UnitRatio
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.JointSmooth

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl GlobalTheory.Fam ValuativeRel IsLocalRing
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SplitInt

variable {D : D7}

theorem mem_latV_iff_at (S : HSp D) (N : Lat S) {P : Pl D → Prop} {v : Pl D} (hv : P v)
    (y : Fin S.rank → AE D) (hy : ∀ i, y i ∈ idAt D (· = v)) :
    y ∈ latV S N P ↔ y ∈ latV S N (· = v) := by
  constructor
  · intro h
    have h2 := GlobalTheory.FinPlLoc.smul_latV v (GlobalTheory.FinPlLoc.idem_mem_intAt (D := D) (· = v)) h
    have e : GlobalTheory.FinPlLoc.idem D (· = v) • y = y := by
      funext i
      rw [Pi.smul_apply, smul_eq_mul]
      exact (GlobalTheory.FinPlLoc.mem_idAt_iff _ _).1 (hy i)
    rwa [e] at h2
  · intro h
    exact GlobalTheory.FinPl.KSplit.latV_mono S N (fun w hw => by subst hw; exact hv) h

section
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem mul_sec (q : SplitPt D k) (a : AE D) (b : k) : a * q.sec b = q.sec (q.pr a * b) := by
  have h := q.sec_pr (a * q.sec b)
  have h2 := q.sec_pr (q.sec b)
  rw [q.pr_sec] at h2
  rw [RingHom.map_mul, q.pr_sec] at h
  rw [h, mul_left_comm, ← h2]

theorem mulVec_sec (q : SplitPt D k) {n : ℕ} (M : Matrix (Fin n) (Fin n) (AE D)) (b : Fin n → k) :
    (M *ᵥ fun i => q.sec (b i)) = fun i => q.sec ((M.map q.pr *ᵥ b) i) := by
  funext i
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply]

  rw [map_sum q.sec]
  exact Finset.sum_congr rfl fun j _ => mul_sec q _ _

theorem mem_KO_of_keeps {Y : Type} [Fintype Y] [DecidableEq Y] (x : GL Y k)
    (h : ∀ y : Y → k, (∀ i, y i ∈ 𝒪[k]) ↔ ∀ i, (x.val *ᵥ y) i ∈ 𝒪[k]) : x ∈ GlobalTheory.SplitWeil.KO k Y := by
  have h1 : ∀ j i : Y, (Pi.single j (1 : k) : Y → k) i ∈ 𝒪[k] := by
    intro j i
    by_cases hij : i = j
    · subst hij; rw [Pi.single_eq_same]; exact one_mem _
    · rw [Pi.single_eq_of_ne hij]; exact zero_mem _
  have hc : ∀ (A : Matrix Y Y k) (i j : Y), (A *ᵥ (Pi.single j (1 : k) : Y → k)) i = A i j := by
    intro A i j
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  have hA : ∀ i j, x.val i j ∈ 𝒪[k] := fun i j => by
    rw [← hc x.val i j]; exact (h _).1 (h1 j) i
  have hB : ∀ i j, (x⁻¹).val i j ∈ 𝒪[k] := fun i j => by
    rw [← hc (x⁻¹).val i j]
    refine (h _).2 ?_ i
    rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
    exact h1 j
  have hinj : Function.Injective ((algebraMap 𝒪[k] k).mapMatrix : Matrix Y Y 𝒪[k] → Matrix Y Y k) :=
    fun a b hab => Matrix.ext fun i j => Subtype.ext (congrFun (congrFun hab i) j)
  let A : Matrix Y Y 𝒪[k] := Matrix.of fun i j => ⟨x.val i j, hA i j⟩
  let B : Matrix Y Y 𝒪[k] := Matrix.of fun i j => ⟨(x⁻¹).val i j, hB i j⟩
  have eA : (algebraMap 𝒪[k] k).mapMatrix A = x.val := rfl
  have eB : (algebraMap 𝒪[k] k).mapMatrix B = (x⁻¹).val := rfl
  refine ⟨⟨A, B, hinj ?_, hinj ?_⟩, Units.ext eA⟩
  · rw [RingHom.map_mul, RingHom.map_one, eA, eB, Units.mul_inv]
  · rw [RingHom.map_mul, RingHom.map_one, eA, eB, Units.inv_mul]

end

theorem mem_KO_of_moves : ∀ {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : SplitPt D k) (S : HSp D) {Y : Type} [Fintype Y] [DecidableEq Y] (F : GlobalTheory.LocMod.Frame k S.rank Y) (N : Lat S) (P : Pl D → Prop), P q.v → IntIn q S F N → ∀ g : GA D S, Moves S g N N P → ∀ x : GL Y k, (mt S g).map q.pr = F.β * x.val * F.γ → x ∈ GlobalTheory.SplitWeil.KO k Y := by
  intro D k _ _ _ _ q S Y _ _ F N P hP hI g hM x hx
  refine mem_KO_of_keeps x fun y => ?_
  have hs : ∀ (b : Fin S.rank → k) i, (fun i => q.sec (b i)) i ∈ idAt D (· = q.v) := fun b i => q.sec_mem_idAt _
  have e : (Formalism.L2.Theta.mt S g).map q.pr *ᵥ (F.β *ᵥ y) = F.β *ᵥ (x.val *ᵥ y) := by
    rw [hx, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc, F.γβ, Matrix.mul_one]
  rw [hI y, hI (x.val *ᵥ y), ← mem_latV_iff_at S N hP _ (hs _), ← mem_latV_iff_at S N hP _ (hs _),
    hM _ (fun i => GlobalTheory.FinPl.KSplit.idAt_mono (fun w hw => by subst hw; exact hP) (hs _ i)), mulVec_sec, e]

end GlobalTheory.SplitInt

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar



noncomputable section

namespace GlobalTheory.SplitFrameLat

open GlobalTheory.FinPl (latV idAt intAt)

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem e_mem_intAt (q : GlobalTheory.FinPl.SplitPt D k) : q.e ∈ intAt D (· = q.v) := by
  refine ⟨GlobalTheory.FrameGlob.e_mem_idAt q, ?_⟩
  have h1 : q.sec 1 = q.e := by
    have := q.sec_pr 1
    rwa [map_one, mul_one] at this
  have h := (q.int_iff 1).1 (one_mem _)
  rwa [h1] at h

theorem smul_mem_latV {V : HSp D} {L : GlobalTheory.FinPl.Lat V} (hL : Submodule.IsLattice D.host.E L) {v : GlobalTheory.FinPl.Pl D}
    {z : Fin V.rank → AE D} (hz : z ∈ latV V L (· = v)) {a : AE D} (ha : a ∈ intAt D (· = v)) :
    a • z ∈ latV V L (· = v) :=
  ((((GlobalTheory.FinPl.localComponents D (· = v)).2 V).2.2.2 L z hL).1 hz).2 v rfl a ha

theorem sec_pr_mul (q : GlobalTheory.FinPl.SplitPt D k) (a : AE D) (c : k) : q.sec (q.pr a * c) = a * q.sec c := by
  calc q.sec (q.pr a * c) = q.sec (q.pr (a * q.sec c)) := by rw [RingHom.map_mul q.pr, q.pr_sec]
    _ = q.e * (a * q.sec c) := q.sec_pr _
    _ = a * q.sec c := by rw [mul_left_comm, ← GlobalTheory.FrameGlob.sec_eq_mul]

theorem sec_int_iff (q : GlobalTheory.FinPl.SplitPt D k) (c : k) :
    toEAf D (q.sec c) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E ↔ c ∈ 𝒪[k] := by
  have h := q.pr_mem_iff (q.sec c)
  rw [q.pr_sec, ← map_mul, ← GlobalTheory.FrameGlob.sec_eq_mul] at h
  exact h.symm

theorem sec_mem_iff (V : HSp D) (t : GA D V) (Λ L : GlobalTheory.FinPl.Lat V) (β : GL (Fin V.rank) (Lev.EAf D))
    (q : GlobalTheory.FinPl.SplitPt D k) (M : Matrix (Fin V.rank) (Fin V.rank) k)
    (hβ : Formalism.L2.DIV.IsFrame β Λ) (hm : GlobalTheory.FinPl.Moves V t Λ L (· = q.v)) (hM : MovedTo (ofSplit q) V t β M)
    (x : Fin V.rank → k) :
    (fun i => q.sec ((M *ᵥ x) i)) ∈ latV V L (· = q.v) ↔ ∀ i, x i ∈ 𝒪[k] := by
  obtain ⟨b, hb⟩ : ∃ b : Matrix (Fin V.rank) (Fin V.rank) (AE D), b.map (toEAf D) = β.val := by
    choose f hf using fun s : Lev.EAf D => GlobalTheory.ResLoc.toEAf_surj (D := D) s
    exact ⟨β.val.map f, by ext i j; simp [hf]⟩
  set s : Fin V.rank → AE D := fun i => q.sec (x i) with hsdef
  have hs : ∀ i, s i ∈ idAt D (· = q.v) := fun i => GlobalTheory.FrameGlob.sec_mem_idAt q _
  have hy : ∀ i, (b *ᵥ s) i ∈ idAt D (· = q.v) := fun i => by
    simp only [Matrix.mulVec, dotProduct]
    exact Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (hs j)
  have hkey : (fun i => q.sec ((M *ᵥ x) i)) = Formalism.L2.Theta.mt V t *ᵥ (b *ᵥ s) := by
    rw [Matrix.mulVec_mulVec, ← hM b hb]
    funext i

    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    exact sec_pr_mul q _ _
  rw [hkey, ← hm _ hy]
  have hbridge : b *ᵥ s ∈ latV V Λ (· = q.v) ↔
      (fun i => Formalism.IndefR.Lev.swapAE D (finPart D ((b *ᵥ s) i))) ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ :=
    ⟨GlobalTheory.LatVHat.latV_mem_hatL D V Λ _ _, GlobalTheory.HatLatV.mem_latV_of_hatL D V Λ _ _ hy⟩
  rw [hbridge, hβ]
  have h2 : (fun i => Formalism.IndefR.Lev.swapAE D (finPart D ((b *ᵥ s) i))) = β.val *ᵥ fun i => toEAf D (s i) := by
    funext i
    change toEAf D ((b *ᵥ s) i) = _
    rw [← hb]
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply]

    rw [map_sum (toEAf D)]
    simp only [RingHom.map_mul]
  rw [h2, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
  exact forall_congr' fun i => sec_int_iff q (x i)

end GlobalTheory.SplitFrameLat

namespace GlobalTheory.SplitFrameLat

open GlobalTheory.FinPl (latV idAt intAt)

theorem latV_eq : ∀ {D : D7} (V : HSp D) (t : GA D V) (Λ L N : GlobalTheory.FinPl.Lat V) (β : GL (Fin V.rank) (Lev.EAf D)) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k) (Y : Type) [Fintype Y] [DecidableEq Y] (F : Frame k V.rank Y) (σ : Fin V.rank ≃ Y), t ∈ GfC V → IsSelfDualC V Λ → Formalism.L2.DIV.IsFrame β Λ → IsSelfDualC V L → IsSelfDualC V N → GlobalTheory.FinPl.Moves V t Λ L (· = q.v) → MovedTo (ofSplit q) V t β (F.β.submatrix id σ) → IntIn q V F N → GlobalTheory.FinPl.latV V L (· = q.v) = GlobalTheory.FinPl.latV V N (· = q.v) := by
  intro D V t Λ L N β k _ _ _ _ q Y _ _ F σ ht hΛ hβ hL hN hm hM hI
  have he := e_mem_intAt q

  have hw : ∀ z : Fin V.rank → AE D, q.e • z ∈ latV V L (· = q.v) ↔ q.e • z ∈ latV V N (· = q.v) := by
    intro z
    set y : Fin V.rank → k := fun i => q.pr (z i) with hydef
    have hz : q.e • z = fun i => q.sec ((F.β *ᵥ (F.γ *ᵥ y)) i) := by
      rw [Matrix.mulVec_mulVec, F.βγ, Matrix.one_mulVec]
      funext i
      simp only [hydef, q.sec_pr, Pi.smul_apply, smul_eq_mul]
    have hL' := sec_mem_iff V t Λ L β q (F.β.submatrix id σ) hβ hm hM ((F.γ *ᵥ y) ∘ σ)
    rw [Matrix.submatrix_mulVec_equiv] at hL'
    have e1 : ((F.γ *ᵥ y) ∘ σ) ∘ σ.symm = F.γ *ᵥ y := by
      funext i; simp
    rw [e1] at hL'
    rw [hz, ← hI]
    have e2 : (fun i => q.sec (((F.β *ᵥ (F.γ *ᵥ y)) ∘ id) i)) = fun i => q.sec ((F.β *ᵥ (F.γ *ᵥ y)) i) := rfl
    rw [e2] at hL'
    rw [hL']
    exact ⟨fun h i => by simpa using h (σ.symm i), fun h i => h (σ i)⟩

  have hce : cA D q.e * cA D q.e = cA D q.e := by rw [← map_mul, q.split.1]
  have hherm : ∀ y x : Fin V.rank → AE D,
      GlobalTheory.IwaPlace.hermAt V (cA D q.e • y) x = GlobalTheory.IwaPlace.hermAt V (cA D q.e • y) (q.e • x) := by
    intro y x
    unfold GlobalTheory.IwaPlace.hermAt
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    simp only [Pi.smul_apply, smul_eq_mul, map_mul]
    linear_combination (-(cA D (x i) * gA V i j * y j)) * hce
  have hbar : ∀ A B : GlobalTheory.FinPl.Lat V, IsSelfDualC V A → IsSelfDualC V B →
      (∀ z, q.e • z ∈ latV V B (· = q.v) → q.e • z ∈ latV V A (· = q.v)) →
      ∀ z : Fin V.rank → AE D, (∀ i, z i ∈ idAt D (· = q.v)) →
        cA D q.e • z ∈ latV V A (· = q.v) → cA D q.e • z ∈ latV V B (· = q.v) := by
    intro A B hA hB hBA z hz h
    have hz' : ∀ i, (cA D q.e • z) i ∈ idAt D (· = q.v) := fun i => Ideal.mul_mem_left _ _ (hz i)
    refine ((GlobalTheory.IwaPlace.LocSD.isSDAt_latV D V B q.v hB).2.2 _ hz').2 fun x hx => ?_
    rw [hherm]
    have hex : q.e • x ∈ latV V A (· = q.v) := hBA x (smul_mem_latV hB.1 hx he)
    exact ((GlobalTheory.IwaPlace.LocSD.isSDAt_latV D V A q.v hA).2.2 _ hz').1 h _ hex
  have hsplit : ∀ z : Fin V.rank → AE D, (∀ i, z i ∈ idAt D (· = q.v)) → q.e • z + cA D q.e • z = z := by
    intro z hz
    obtain ⟨ε, hε, hs⟩ := q.above
    rw [← add_smul, hs]
    funext i
    exact ((GlobalTheory.T.placeIdempotent_acts_on_supportedAndOff D q.v ε hε).1 (z i)).1 (hz i)
  have hgen : ∀ A B : GlobalTheory.FinPl.Lat V, IsSelfDualC V A → IsSelfDualC V B →
      (∀ z, q.e • z ∈ latV V A (· = q.v) ↔ q.e • z ∈ latV V B (· = q.v)) →
      latV V A (· = q.v) ≤ latV V B (· = q.v) := by
    intro A B hA hB hAB z hz
    have hs := GlobalTheory.FinPl.FrameLat.latV_supp hz
    have h1 : q.e • z ∈ latV V A (· = q.v) := smul_mem_latV hA.1 hz he
    have h3 : cA D q.e • z = z - q.e • z := by
      rw [eq_sub_iff_add_eq']
      exact hsplit z hs
    have h2 : cA D q.e • z ∈ latV V A (· = q.v) := by
      rw [h3]
      exact sub_mem hz h1
    have := add_mem ((hAB z).1 h1) (hbar A B hA hB (fun z => (hAB z).2) z hs h2)
    rwa [hsplit z hs] at this
  exact le_antisymm (hgen L N hL hN hw) (hgen N L hN hL fun z => (hw z).symm)

end GlobalTheory.SplitFrameLat

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl GlobalTheory.Fam ValuativeRel IsLocalRing
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SplitOnto

variable {D : D7}

theorem eq_zero_at_off (P : Pl D → Prop) {a : AE D} (h1 : a ∈ idAt D P) (h2 : a ∈ idOff D P) : a = 0 := by
  obtain ⟨ε, -, -, -, hA, hO⟩ := (GlobalTheory.T.adelicPoint_components_atPlaces_lattices_vacua D P).1
  rw [← (hA a).1 h1]
  exact (hO a).1 h2

theorem mulVec_off {S : HSp D} {P : Pl D → Prop} {b : GA D S} (hb : b ∈ grpOff S P) {y : Fin S.rank → AE D}
    (hy : ∀ i, y i ∈ idAt D P) : mt S b *ᵥ y = y := by
  rw [grpOff, PlacesAdeles.mem_congGrp] at hb
  have key : (mt S b - 1) *ᵥ y = 0 := by
    funext i
    simp only [Matrix.mulVec, dotProduct, Pi.zero_apply]
    refine Finset.sum_eq_zero fun j _ => ?_
    apply eq_zero_at_off P
    · exact Ideal.mul_mem_left _ _ (hy j)
    · exact Ideal.mul_mem_right _ _ (by simpa using hb i j)
  rw [Matrix.sub_mulVec, sub_eq_zero, Matrix.one_mulVec] at key
  exact key

theorem moves_off {S : HSp D} {L : Lat S} {P : Pl D → Prop} {b : GA D S} (hb : b ∈ grpOff S P) :
    Moves S b L L P := by
  intro y hy
  rw [mulVec_off hb hy]

theorem moves_one {S : HSp D} {L : Lat S} {P : Pl D → Prop} : Moves S 1 L L P := by
  intro y _
  rw [PlacesAdeles.mt_one, Matrix.one_mulVec]

theorem moves_list_prod {S : HSp D} {L : Lat S} {P : Pl D → Prop} :
    ∀ l : List (GA D S), (∀ a ∈ l, Moves S a L L P) → Moves S l.prod L L P
  | [], _ => by rw [List.prod_nil]; exact moves_one
  | a :: l, h => by
    rw [List.prod_cons]
    exact PlacesAdeles.moves_mul (h a List.mem_cons_self) (moves_list_prod l fun b hb => h b (List.mem_cons_of_mem _ hb))

theorem prod_ofFn_single {M : Type*} [Monoid M] :
    ∀ {r : ℕ} (f : Fin r → M) (i : Fin r), (∀ j, j ≠ i → f j = 1) → (List.ofFn f).prod = f i
  | 0, _, i, _ => i.elim0
  | r + 1, f, i, h => by
    rw [List.ofFn_succ, List.prod_cons]
    rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i', rfl⟩
    · have hprod : (List.ofFn (fun j : Fin r => f j.succ)).prod = 1 := by
        apply List.prod_eq_one
        rw [List.forall_mem_ofFn_iff]
        exact fun j => h j.succ (Fin.succ_ne_zero j)
      rw [hprod, mul_one]
    · rw [h 0 (Fin.succ_ne_zero i').symm, one_mul]
      exact prod_ofFn_single (fun j => f j.succ) i' fun j hj => h _ fun e => hj (Fin.succ_injective _ e)

def locHom (S : HSp D) {k : Type} [Ring k] (f : AE D →+* k) : GA D S →* Matrix (Fin S.rank) (Fin S.rank) k where
  toFun a := (mt S a).map f
  map_one' := by rw [PlacesAdeles.mt_one]; exact Matrix.map_one f f.map_zero f.map_one
  map_mul' a b := by rw [PlacesAdeles.mt_mul]; exact Matrix.map_mul

section Place

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem pr_off (q : SplitPt D k) {a : AE D} (ha : a ∈ idOff D (· = q.v)) : q.pr a = 0 := by
  have h1 : q.e * a = 0 := eq_zero_at_off (· = q.v)
    (Ideal.mul_mem_right a _ (FrameLat.e_mem_idAt (p := q))) (Ideal.mul_mem_left _ q.e ha)
  have h2 : q.pr q.e = 1 := by rw [← FrameLat.sec_one (p := q), q.pr_sec]
  calc q.pr a = q.pr q.e * q.pr a := by rw [h2, one_mul]
    _ = 0 := by rw [← map_mul, h1, map_zero]

theorem map_off (q : SplitPt D k) {S : HSp D} {b : GA D S} (hb : b ∈ grpOff S (· = q.v)) :
    (mt S b).map q.pr = 1 := by
  rw [grpOff, PlacesAdeles.mem_congGrp] at hb
  ext i j
  have h := pr_off q (hb i j)
  rw [map_sub, sub_eq_zero] at h
  rw [Matrix.map_apply, h, Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp

theorem one_place (S : HSp D) (N : Lat S) (hN : IsSelfDualC S N) (q : SplitPt D k) {Y : Type} [Fintype Y] [DecidableEq Y]
    (F : GlobalTheory.LocMod.Frame k S.rank Y) (hI : IntIn q S F N) (x : GL Y k) (hx : x ∈ GlobalTheory.SplitWeil.KO k Y) :
    ∃ g, InK S N (· = q.v) g ∧ (mt S g).map q.pr = F.β * x.val * F.γ := by
  classical
  have H := (GlobalTheory.LocGrp.local_groups D k (GlobalTheory.LocMod.Place.ofSplitPt q)).1 S Y F
  choose glf hglf using fun gk => (H.1 gk).exists
  let gl : GL Y k →* GA D S := MonoidHom.mk' glf fun a b =>
    (H.1 (a * b)).unique (hglf (a * b)) (H.2.2 _ _ _ _ (hglf a) (hglf b))
  let β : GlobalTheory.FinPl.Frame q S Y := ⟨F.β, F.γ, F.βγ, F.γβ, gl, fun g => (hglf g).1, fun g => (hglf g).2⟩
  obtain ⟨Λ, -, hΛ, hK⟩ := GlobalTheory.FinPl.FrameLat.exists_lat D k q S Y β N hN
  have hmem : ∀ y : Y → k, y ∈ Λ ↔ ∀ j, y j ∈ 𝒪[k] := fun y => (hΛ y).trans (hI y).symm
  obtain ⟨x₀, rfl⟩ := hx
  have hint : ∀ (z : GL Y 𝒪[k]) (y : Y → k), (∀ j, y j ∈ 𝒪[k]) →
      ∀ j, (Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k) z • y) j ∈ 𝒪[k] := by
    intro z y hy j
    change ((Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k) z).val *ᵥ y) j ∈ 𝒪[k]
    simp only [Matrix.mulVec, dotProduct]
    exact sum_mem fun l _ => mul_mem (z.val j l).2 (hy l)
  have hstab : Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k) x₀ • Λ = Λ := by
    ext y
    rw [GlobalTheory.LatPair.mem_smul_iff, hmem, hmem]
    constructor
    · intro h
      have := hint x₀ _ h
      rwa [smul_inv_smul] at this
    · intro h
      rw [← map_inv]
      exact hint x₀⁻¹ y h
  exact ⟨β.gl _, (hK _).2 hstab, (hglf _).2⟩

end Place

theorem exists_of_local : ∀ {D : D7} (S : HSp D) (N : Lat S), IsSelfDualC S N → ∀ {r : ℕ} (k : Fin r → Type) [∀ i, Field (k i)] [∀ i, ValuativeRel (k i)] [∀ i, TopologicalSpace (k i)] [∀ i, IsNonarchimedeanLocalField (k i)] (q : (i : Fin r) → SplitPt D (k i)) (Y : Fin r → Type) [∀ i, Fintype (Y i)] [∀ i, DecidableEq (Y i)] (F : (i : Fin r) → GlobalTheory.LocMod.Frame (k i) S.rank (Y i)), Function.Injective (fun i => (q i).v) → (∀ i, IntIn (q i) S (F i) N) → ∀ x : (i : Fin r) → GL (Y i) (k i), (∀ i, x i ∈ GlobalTheory.SplitWeil.KO (k i) (Y i)) → ∃ g, InK S N (fun p => ∃ i, (q i).v = p) g ∧ ∀ i, (mt S g).map (q i).pr = (F i).β * (x i).val * (F i).γ := by
  intro D S N hN r k _ _ _ _ q Y _ _ F hinj hI x hx
  classical
  choose g hgK hgm using fun i => one_place S N hN (q i) (F i) (hI i) (x i) (hx i)
  have hgrp : ∀ i, g i ∈ grpAt S (· = (q i).v) := fun i => (hgK i).1
  have hoff : ∀ i j, j ≠ i → g j ∈ grpOff S (· = (q i).v) := fun i j hji =>
    PlacesAdeles.congGrp_mono (PlacesAdeles.idAt_le_idOff (fun e => hji (hinj e).symm)) (hgrp j)
  refine ⟨(List.ofFn g).prod, ⟨?_, ?_⟩, ?_⟩
  · refine _root_.list_prod_mem fun a ha => ?_
    obtain ⟨j, rfl⟩ := (List.mem_ofFn' _ _).1 ha
    exact PlacesAdeles.congGrp_mono (PlacesAdeles.idAt_single_le ⟨j, rfl⟩) (hgrp j)
  · have hlat := ((GlobalTheory.T.adelicPoint_components_atPlaces_lattices_vacua D (fun p => ∃ i, (q i).v = p)).2 S).2.2.2 N
    have hloc : ∀ i, Moves S (List.ofFn g).prod N N (· = (q i).v) := fun i =>
      moves_list_prod _ fun a ha => by
        obtain ⟨j, rfl⟩ := (List.mem_ofFn' _ _).1 ha
        by_cases hji : j = i
        · subst hji; exact (hgK j).2
        · exact moves_off (hoff i j hji)
    intro y hy
    rw [hlat y hN.1, hlat _ hN.1]
    have hy' := PlacesAdeles.supp_mulVec S _ (List.ofFn g).prod hy
    have hey : ∀ v e, e ∈ intAt D (· = v) → ∀ i, (e • y) i ∈ idAt D (· = v) := fun v e he i => by
      simpa [smul_eq_mul] using Ideal.mul_mem_right (y i) _ he.1
    constructor
    · rintro ⟨-, h2⟩
      refine ⟨hy', fun v hv e he => ?_⟩
      obtain ⟨i, rfl⟩ := hv
      rw [← Matrix.mulVec_smul]
      exact (hloc i _ (hey _ e he)).1 (h2 _ ⟨i, rfl⟩ e he)
    · rintro ⟨-, h2⟩
      refine ⟨hy, fun v hv e he => ?_⟩
      obtain ⟨i, rfl⟩ := hv
      have := h2 _ ⟨i, rfl⟩ e he
      rw [← Matrix.mulVec_smul] at this
      exact (hloc i _ (hey _ e he)).2 this
  · intro i
    change locHom S (q i).pr (List.ofFn g).prod = _
    rw [map_list_prod, List.map_ofFn, prod_ofFn_single _ i]
    · exact hgm i
    · intro j hji
      exact map_off (q i) (hoff i j hji)

end GlobalTheory.SplitOnto

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.thetaChainStep_fockVector_sphericalOffS : ∀ D : D7, ForStep D fun c k s s' p => (∀ φ, GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.IsFockVec c.ψ c.θ s.V s'.V (cart s.M) (cart s'.M) (p.pt φ) ∧ GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.IsSphOff c.ψ s.V s'.V s.Λ s'.Λ c.S (p.pt φ)) ∧ GlobalTheory.LFun.UnrOff (c.chS (k + 1)) (c.S : Set (HeightOneSpectrum (𝓞 D.host.F))) ∧ GlobalTheory.LFun.UnrOff (c.chT (k + 1)) (c.S : Set (HeightOneSpectrum (𝓞 D.host.F))) := by
  first | exact @GlobalTheory.ChainOnto.fock_sph | exact GlobalTheory.ChainOnto.fock_sph | (intros; apply GlobalTheory.ChainOnto.fock_sph <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.SeeSaw GlobalTheory.AdForm GlobalTheory.LocMod

theorem _root_.GlobalTheory.T.integral_matrix_split_place_mem_stdHomLattice : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k) (S T : HSp D) (a₀ : D.host.E), a₀ ∈ (D.host.AA : Set D.host.E) → q.pr (incA D a₀) ≠ 0 → ∀ (FS : Frame k S.rank (Fin S.rank)) (FT : Frame k T.rank (Fin T.rank)), FT.β = 1 → FT.γ = 1 → FS.γ = q.pr (incA D a₀) • (HSpace.gram S).map (fun a => q.pr (incA D a)) → ∀ t : Matrix (Fin T.rank) (Fin S.rank) k, (∀ r s, t r s ∈ 𝒪[k]) → (Place.ofSplitPt q).up FS FT t ∈ stdHom S T := by
  first | exact @GlobalTheory.SplitUpStd.int_up_mem_stdHom | exact GlobalTheory.SplitUpStd.int_up_mem_stdHom | (intros; apply GlobalTheory.SplitUpStd.int_up_mem_stdHom <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.LocMod

theorem _root_.GlobalTheory.T.besselFlatMap_local_unipotent_translation_law : ∀ (D : D7), FlatLaw D → GlobalTheory.FinPl.FlatLaws D → OmLoc D → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (p : Place D k) (ν : Measure k), ν.IsAddHaarMeasure → ∀ (ψ : AddChar (AF D.host.F) ℂ) (ψk : AddChar k Circle), p.IsChar ψ ψk → ∀ (ρ : ℕ) (B : BesLev D ρ) (J : JacLev D ρ) (st : StepBF ψ B J) (s : k), s ≠ 0 → ∀ (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c : ℕ) (FA : Frame k B.A.rank n') (F₀ : Frame k B.V₀.rank (n' ⊕ Unit)) (FV : Frame k B.V.rank (n' ⊕ Fin (c + 1))) (G₀ : Frame k J.W₀.rank n) (FW : Frame k J.W.rank (n ⊕ Fin c)), p.IsCoreFrame B s FA F₀ → p.IsBesFrame B s FA FV → p.IsJacFrame J s (p.hz B) G₀ FW → ∀ (Tm : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) →ₗ[ℂ] (WO B.V J.W → ℂ)), p.IsModel ψ FV FW Tm → ∀ u : GL (Fin c) k, GlobalTheory.RootEx.embA n u ∈ GlobalTheory.RootEx.N k n c (ρ + 1) → (∀ l l' : Fin c, l.val < ρ → ρ ≤ l'.val → u.val l l' = 0) → ∀ (Φ Φ' : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)), (∀ t, Φ'.1 t = Φ.1 (((GlobalTheory.RootEx.embA n u)⁻¹).val * t)) → flatBF st (Tm Φ') = (ψk (-GlobalTheory.RootEx.simpleSum (GlobalTheory.RootEx.embA n u)) : ℂ) • flatBF st (Tm Φ) := by
  first | exact @GlobalTheory.FlatUnip.flatBF_unip | exact GlobalTheory.FlatUnip.flatBF_unip | (intros; apply GlobalTheory.FlatUnip.flatBF_unip <;> assumption)
end
