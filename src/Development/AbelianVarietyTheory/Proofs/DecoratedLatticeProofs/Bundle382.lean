module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle258
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle144
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle190
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle331
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle191
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceBaseVacuumDatumExistsUnique
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle186
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle149
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle320
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualSplitComponentIsLatticeStabilizerEq
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle347
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
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsUnitarySupportedAtPlaceOfMulEqIdem
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.JointSmooth
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiStarOfMid
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle001
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle019
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.UnitRatio
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ValuationDetOfMemKO
import Formalism.LocalToGlobal.Columns.CoefficientsModP.WeTransposeWordTransposeWord
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle076

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl GlobalTheory.LatPair
open scoped Pointwise

noncomputable section

namespace GlobalTheory.FinPlMovesLoc

variable {D : D7}

theorem idAt_mono {P Q : Pl D → Prop} (h : ∀ w, Q w → P w) {a : AE D} (ha : a ∈ idAt D Q) : a ∈ idAt D P := by
  unfold idAt at ha ⊢
  obtain ⟨h0, hw⟩ := Ideal.mem_inf.1 ha
  refine Ideal.mem_inf.2 ⟨h0, (Submodule.mem_iInf _).2 fun w => ?_⟩
  exact (Submodule.mem_iInf _).1 hw ⟨w.1, fun hq => w.2 (h _ hq)⟩

theorem latV_mono {S : HSp D} {L : Lat S} {P Q : Pl D → Prop} (h : ∀ w, Q w → P w) {y : Fin S.rank → AE D}
    (hy : y ∈ GlobalTheory.FinPl.latV S L Q) : y ∈ GlobalTheory.FinPl.latV S L P := by
  unfold GlobalTheory.FinPl.latV GlobalTheory.FinPl.latMul at hy ⊢
  refine AddSubgroup.closure_mono ?_ hy
  rintro z ⟨α, hαi, hα, a, ha, x, hx, rfl⟩
  exact ⟨α, hαi, fun w hw => hα w (fun hq => hw (h w hq)), a, ha, x, hx, rfl⟩

theorem mulVec_idAt {S : HSp D} (g : GA D S) {Q : Pl D → Prop} {y : Fin S.rank → AE D} (hy : ∀ i, y i ∈ idAt D Q) :
    ∀ i, (mt S g *ᵥ y) i ∈ idAt D Q := by
  intro i
  simp only [Matrix.mulVec, dotProduct]
  exact Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (hy j)

theorem latV_at_iff {S : HSp D} {L : Lat S} {P : Pl D → Prop} {v : Pl D} (hv : P v) {y : Fin S.rank → AE D}
    (hy : ∀ i, y i ∈ idAt D (· = v)) : y ∈ GlobalTheory.FinPl.latV S L (· = v) ↔ y ∈ GlobalTheory.FinPl.latV S L P := by
  constructor
  · exact latV_mono (fun w hw => hw ▸ hv)
  · intro h
    have h1 := GlobalTheory.FinPlLoc.smul_latV v (GlobalTheory.FinPlLoc.idem_mem_intAt (· = v)) h
    have h2 : GlobalTheory.FinPlLoc.idem D (· = v) • y = y := by
      funext i
      rw [Pi.smul_apply, smul_eq_mul]
      exact (GlobalTheory.FinPlLoc.mem_idAt_iff _ _).1 (hy i)
    rwa [h2] at h1

theorem moves_iff : ∀ {D : D7} (S : HSp D) (g : GA D S) (L : GlobalTheory.FinPl.Lat S), Submodule.IsLattice D.host.E L →
    ∀ (P : GlobalTheory.FinPl.Pl D → Prop), GlobalTheory.FinPl.Moves S g L L P ↔ ∀ v, P v → GlobalTheory.FinPl.Moves S g L L (· = v) := by
  intro D S g L hL P
  constructor
  · intro hM v hv y hy
    have hyP : ∀ i, y i ∈ idAt D P := fun i => idAt_mono (fun w hw => hw ▸ hv) (hy i)
    rw [latV_at_iff hv hy, latV_at_iff hv (mulVec_idAt g hy)]
    exact hM y hyP
  · intro hM y hy
    rw [GlobalTheory.FinPlLoc.part_lat P S L y hL, GlobalTheory.FinPlLoc.part_lat P S L _ hL]
    have hsupp : ∀ v, ∀ e ∈ intAt D (· = v), ∀ i, (e • y) i ∈ idAt D (· = v) := fun v e he i => by
      rw [Pi.smul_apply, smul_eq_mul]; exact Ideal.mul_mem_right _ _ he.1
    have hcomm : ∀ e : AE D, e • (mt S g *ᵥ y) = mt S g *ᵥ (e • y) := fun e => (Matrix.mulVec_smul _ _ _).symm
    constructor
    · rintro ⟨-, h⟩
      refine ⟨mulVec_idAt g hy, fun v hv e he => ?_⟩
      rw [hcomm]
      exact (hM v hv (e • y) (hsupp v e he)).1 (h v hv e he)
    · rintro ⟨-, h⟩
      refine ⟨hy, fun v hv e he => ?_⟩
      refine (hM v hv (e • y) (hsupp v e he)).2 ?_
      rw [← hcomm]
      exact h v hv e he

end GlobalTheory.FinPlMovesLoc
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.LocMod GlobalTheory.MiS ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Fam

noncomputable section

namespace GlobalTheory.Fam.OffLevel

open GlobalTheory.FinPl GlobalTheory.FinPl.KSplit

variable {D : D7}

theorem mem_latV_at_iff_all (S : HSp D) (L : Lat S) (p : Pl D) {z : Fin S.rank → AE D}
    (hz : ∀ i, z i ∈ idAt D (· = p)) : z ∈ latV S L (· = p) ↔ z ∈ latV S L (fun _ => True) := by
  constructor
  · exact fun h => latV_mono S L (fun _ _ => trivial) h
  · intro h
    have h1 := ((mem_latV_iff_parts S L (fun _ => True) {p}
      (fun i => idAt_mono (fun _ _ => trivial) (hz i))).1 h).1
    have e : eQ {p} • z = z := funext fun i =>
      eQ_mul_of_in (P := fun _ => True) {p}
        (idAt_mono (fun w hw => ⟨trivial, Finset.mem_singleton.2 hw⟩) (hz i))
    rw [e] at h1
    exact latV_mono S L (fun w hw => Finset.mem_singleton.1 hw.2) h1

theorem latV_eq_of_moves (S : HSp D) (g : GA D S) (Λ N M : Lat S) (p : Pl D)
    (hN : Moves S g Λ N (· = p)) (hM : Moves S g Λ M (fun _ => True)) :
    latV S N (· = p) = latV S M (· = p) := by
  have key : ∀ z : Fin S.rank → AE D, (∀ i, z i ∈ idAt D (· = p)) →
      (z ∈ latV S N (· = p) ↔ z ∈ latV S M (· = p)) := by
    intro z hz
    set y := mt S g⁻¹ *ᵥ z with hy
    have hys : ∀ i, y i ∈ idAt D (· = p) := mulVec_mem S _ hz
    have hgy : mt S g *ᵥ y = z := by
      rw [hy, Matrix.mulVec_mulVec, ← KSplit.mt_mul, mul_inv_cancel]
      exact Matrix.one_mulVec z
    rw [← hgy, ← hN y hys, mem_latV_at_iff_all S M p (by rw [hgy]; exact hz),
      ← hM y (fun i => idAt_mono (fun _ _ => trivial) (hys i)), mem_latV_at_iff_all S Λ p hys]
  ext z
  constructor
  · intro h; exact (key z (GlobalTheory.FinPlLoc.latV_idAt h)).1 h
  · intro h; exact (key z (GlobalTheory.FinPlLoc.latV_idAt h)).2 h

end GlobalTheory.Fam.OffLevel

end

end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FinPl.LocAgree

open GlobalTheory.FinPl GlobalTheory.FinPl.KSplit

variable {D : D7}

theorem latV_congr (S : HSp D) (L : Lat S) {P P' : Pl D → Prop} (h : ∀ w, P w ↔ P' w) :
    latV S L P = latV S L P' :=
  le_antisymm (latV_mono S L fun w => (h w).1) (latV_mono S L fun w => (h w).2)

theorem latV_le_of_int_smul_on (S : HSp D) (L M : Lat S) (d : ℤ) (hd : d ≠ 0)
    (hLM : ∀ x ∈ L, d • x ∈ M) (R : Pl D → Prop) (hR : ∀ v, R v → ((d : 𝓞 D.host.F)) ∉ v.asIdeal) :
    latV S L R ≤ latV S M R := by
  rw [latV, latMul, AddSubgroup.closure_le]
  rintro y ⟨α, hα, hsupp, a, ha, x, hx, rfl⟩
  rw [Set.mem_singleton_iff] at ha
  subst ha
  apply AddSubgroup.subset_closure
  refine ⟨((d : D.host.F))⁻¹ • α, ?_, ?_, 1, rfl, d • x, hLM x hx, ?_⟩
  · intro w
    rw [map_smul]
    by_cases hw : R w
    · have hval : Valued.v (algebraMap D.host.F (w.adicCompletion D.host.F) (d : D.host.F)) = 1 := by
        have h1 := (w.valuation_eq_one_iff_notMem (K := D.host.F)).mpr (hR w hw)
        have h2 := w.valuedAdicCompletion_eq_valuation' (K := D.host.F) ((d : D.host.F))
        have h4 : (((d : 𝓞 D.host.F)) : D.host.F) = ((d : D.host.F)) :=
          map_intCast (algebraMap (𝓞 D.host.F) D.host.F) _
        exact h2.trans (h4 ▸ h1)
      have hαw := hα w
      rw [HeightOneSpectrum.mem_adicCompletionIntegers] at hαw ⊢
      rw [Algebra.smul_def, map_mul, map_inv₀, map_inv₀, hval, inv_one, one_mul]
      exact hαw
    · rw [hsupp w hw, smul_zero]
      exact zero_mem _
  · intro w hw
    rw [map_smul, hsupp w hw, smul_zero]
  · funext i
    exact pairA_tmul_int_gen d hd α (x i)

theorem latV_le_finite (S : HSp D) (L N : Lat S) (d : ℤ) (hd : d ≠ 0) (hLN : ∀ x ∈ L, d • x ∈ N)
    (P : Pl D → Prop) (hP : ∀ w, P w → latV S L (· = w) = latV S N (· = w)) (T : Finset (Pl D)) :
    latV S L (fun p => P p ∧ p ∈ T) ≤ latV S N (fun p => P p ∧ p ∈ T) := by
  classical
  induction T using Finset.induction_on with
  | empty =>
    exact latV_le_of_int_smul_on S L N d hd hLN _ fun v hv => absurd hv.2 (Finset.notMem_empty v)
  | insert a T' ha ih =>
    intro z hz
    have hs := GlobalTheory.FinPlLoc.latV_idAt hz
    obtain ⟨h1, h2⟩ := (mem_latV_iff_parts S L _ {a} hs).1 hz
    rw [mem_latV_iff_parts S N _ {a} hs]
    constructor
    · by_cases hPa : P a
      · have hiff : ∀ w, ((P w ∧ w ∈ insert a T') ∧ w ∈ ({a} : Finset (Pl D))) ↔ w = a := by
          intro w
          simp only [Finset.mem_insert, Finset.mem_singleton]
          constructor
          · exact fun h => h.2
          · rintro rfl; exact ⟨⟨hPa, Or.inl rfl⟩, rfl⟩
        rw [latV_congr S L hiff, hP a hPa] at h1
        rw [latV_congr S N hiff]
        exact h1
      · refine latV_le_of_int_smul_on S L N d hd hLN _ (fun v hv => ?_) h1
        exact absurd (Finset.mem_singleton.1 hv.2 ▸ hv.1.1) hPa
    · have hiff : ∀ w, ((P w ∧ w ∈ insert a T') ∧ w ∉ ({a} : Finset (Pl D))) ↔ (P w ∧ w ∈ T') := by
        intro w
        simp only [Finset.mem_insert, Finset.mem_singleton]
        constructor
        · rintro ⟨⟨hw, h | h⟩, hne⟩
          · exact absurd h hne
          · exact ⟨hw, h⟩
        · rintro ⟨hw, h⟩
          exact ⟨⟨hw, Or.inr h⟩, fun e => ha (e ▸ h)⟩
      rw [latV_congr S L hiff] at h2
      rw [latV_congr S N hiff]
      exact ih h2

theorem latV_le_of_local (S : HSp D) (L N : Lat S) (d : ℤ) (hd : d ≠ 0) (hLN : ∀ x ∈ L, d • x ∈ N)
    (P : Pl D → Prop) (hP : ∀ w, P w → latV S L (· = w) = latV S N (· = w)) : latV S L P ≤ latV S N P := by
  classical
  set T := (finite_places_int (D := D) d hd).toFinset
  intro y hy
  have hs := GlobalTheory.FinPlLoc.latV_idAt hy
  obtain ⟨h1, h2⟩ := (mem_latV_iff_parts S L P T hs).1 hy
  rw [mem_latV_iff_parts S N P T hs]
  refine ⟨latV_le_finite S L N d hd hLN P hP T h1, latV_le_of_int_smul_on S L N d hd hLN _ (fun v hv => ?_) h2⟩
  intro hmem
  exact hv.2 ((Set.Finite.mem_toFinset _).2 hmem)

theorem latV_eq_of_local : ∀ {D : D7} (S : HSp D) (L N : GlobalTheory.FinPl.Lat S) (P : GlobalTheory.FinPl.Pl D → Prop),
    Submodule.IsFullLattice D.host.E L → Submodule.IsFullLattice D.host.E N →
    (∀ w, P w → GlobalTheory.FinPl.latV S L (· = w) = GlobalTheory.FinPl.latV S N (· = w)) →
    GlobalTheory.FinPl.latV S L P = GlobalTheory.FinPl.latV S N P := by
  intro D S L N P hL hN hP
  obtain ⟨d₁, hd₁, h₁⟩ := exists_int_smul_le L N hL.fg hN.span_eq_top
  obtain ⟨d₂, hd₂, h₂⟩ := exists_int_smul_le N L hN.fg hL.span_eq_top
  exact le_antisymm (latV_le_of_local S L N d₁ hd₁ h₁ P hP)
    (latV_le_of_local S N L d₂ hd₂ h₂ P fun w hw => (hP w hw).symm)

end GlobalTheory.FinPl.LocAgree

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open GlobalTheory.FinPl
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FinPl.LineAct

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

section Generic

variable {p : SplitPt D k} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {n n' : Type} [Fintype n] [DecidableEq n]
  [Fintype n'] [DecidableEq n'] {α : Frame p S n'} {β : Frame p T n} {LS : Lat S} {LT : Lat T} {f₀ f : WO S T → ℂ}
  {Ψ Ψ' : Matrix n n' k → ℂ}

theorem over_trans (h : Over ψ α β LS LT f₀ Ψ f) {x : WO S T} (hx : IsHalf p.e x) (hΨ' : Ψ' ∈ SB (Matrix n n' k))
    (he : ∀ t, IsHalf p.e t → Ψ' (rd α β t) = Ψ (rd α β (t + x))) : Over ψ α β LS LT f₀ Ψ' (heisO ψ S T x f) := by
  obtain ⟨hS, hT, hV, hΨ, hex, hall⟩ := h
  have hsb := GlobalTheory.FinPl.OverProof.isSBHalf_extFun D k p n n' S T α β LS LT hS hT Ψ hΨ
  have hfun : extFun α β Ψ' = fun t => extFun α β Ψ (t + x) := by
    funext t
    have hc : IsHalf p.e (t + x) ↔ IsHalf p.e t := forall_congr' fun i => forall_congr' fun j => by
      rw [Matrix.add_apply, mul_add, hx i j, add_left_inj]
    unfold extFun
    by_cases ht : IsHalf p.e t
    · rw [if_pos ht, if_pos (hc.2 ht), he t ht]
    · rw [if_neg ht, if_neg (fun h' => ht (hc.1 h'))]
  refine ⟨hS, hT, hV, hΨ', hex, fun Tm hTm => ?_⟩
  show heisO ψ S T x f = Tm (extFun α β Ψ')
  rw [hall Tm hTm, hfun, hTm.trans _ hsb x hx]

theorem over_modul (h : Over ψ α β LS LT f₀ Ψ f) {y : WO S T} (hy : IsHalf (cA D p.e) y)
    (hΨ' : Ψ' ∈ SB (Matrix n n' k))
    (he : ∀ t, IsHalf p.e t → Ψ' (rd α β t) = ψ (symplO S T t y) * Ψ (rd α β t)) :
    Over ψ α β LS LT f₀ Ψ' (heisO ψ S T y f) := by
  obtain ⟨hS, hT, hV, hΨ, hex, hall⟩ := h
  have hsb := GlobalTheory.FinPl.OverProof.isSBHalf_extFun D k p n n' S T α β LS LT hS hT Ψ hΨ
  have hfun : extFun α β Ψ' = fun t => ψ (symplO S T t y) * extFun α β Ψ t := by
    funext t
    unfold extFun
    by_cases ht : IsHalf p.e t
    · rw [if_pos ht, if_pos ht, he t ht]
    · rw [if_neg ht, if_neg ht, mul_zero]
  refine ⟨hS, hT, hV, hΨ', hex, fun Tm hTm => ?_⟩
  show heisO ψ S T y f = Tm (extFun α β Ψ')
  rw [hall Tm hTm, hfun, hTm.modul _ hsb y hy]

end Generic

section SBLemmas

variable {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']

theorem tensCol_mul_mem {Ψ : Matrix n n' k → ℂ} {a g : (n → k) → ℂ} (hg : IsLocallyConstant g)
    (h : tensCol Ψ a ∈ SB (Matrix n (n' ⊕ Fin 1) k)) :
    tensCol Ψ (fun y => g y * a y) ∈ SB (Matrix n (n' ⊕ Fin 1) k) := by
  have e : tensCol Ψ (fun y => g y * a y) =
      (fun x : Matrix n (n' ⊕ Fin 1) k => g fun i => x i (Sum.inr 0)) * tensCol Ψ a := by
    funext x; simp only [tensCol, Pi.mul_apply]; ring
  rw [e]
  exact ⟨(hg.comp_continuous (by fun_prop)).mul h.1, h.2.mul_left⟩

theorem tensRow_mul_mem {Ψ : Matrix n' n k → ℂ} {b g : (n → k) → ℂ} (hg : IsLocallyConstant g)
    (h : tensRow Ψ b ∈ SB (Matrix (n' ⊕ Fin 1) n k)) :
    tensRow Ψ (fun y => g y * b y) ∈ SB (Matrix (n' ⊕ Fin 1) n k) := by
  have e : tensRow Ψ (fun y => g y * b y) =
      (fun x : Matrix (n' ⊕ Fin 1) n k => g (x (Sum.inr 0))) * tensRow Ψ b := by
    funext x; simp only [tensRow, Pi.mul_apply]; ring
  rw [e]
  exact ⟨(hg.comp_continuous (by fun_prop)).mul h.1, h.2.mul_left⟩

theorem tensCol_sub_mem {Ψ : Matrix n n' k → ℂ} {a : (n → k) → ℂ} (t : n → k)
    (h : tensCol Ψ a ∈ SB (Matrix n (n' ⊕ Fin 1) k)) :
    tensCol Ψ (fun y => a (y - t)) ∈ SB (Matrix n (n' ⊕ Fin 1) k) := by
  let M : Matrix n (n' ⊕ Fin 1) k := Matrix.of fun i j => Sum.elim (fun _ => 0) (fun _ => t i) j
  have e : tensCol Ψ (fun y => a (y - t)) = tensCol Ψ a ∘ Homeomorph.subRight M := by
    funext x
    simp only [tensCol, Function.comp_apply, Homeomorph.subRight_apply]
    congr 2
    all_goals first | (ext i j; simp [M]) | (funext i; simp [M])
  rw [e]
  exact ⟨h.1.comp_continuous (Homeomorph.subRight M).continuous, h.2.comp_homeomorph _⟩

theorem tensRow_sub_mem {Ψ : Matrix n' n k → ℂ} {b : (n → k) → ℂ} (t : n → k)
    (h : tensRow Ψ b ∈ SB (Matrix (n' ⊕ Fin 1) n k)) :
    tensRow Ψ (fun y => b (y - t)) ∈ SB (Matrix (n' ⊕ Fin 1) n k) := by
  let M : Matrix (n' ⊕ Fin 1) n k := Matrix.of fun i j => Sum.elim (fun _ => 0) (fun _ => t j) i
  have e : tensRow Ψ (fun y => b (y - t)) = tensRow Ψ b ∘ Homeomorph.subRight M := by
    funext x
    simp only [tensRow, Function.comp_apply, Homeomorph.subRight_apply]
    congr 2
    all_goals first | (ext i j; simp [M]) | (funext i; simp [M])
  rw [e]
  exact ⟨h.1.comp_continuous (Homeomorph.subRight M).continuous, h.2.comp_homeomorph _⟩

end SBLemmas

end GlobalTheory.FinPl.LineAct

end

noncomputable section
namespace GlobalTheory.FinPl.LineAct

theorem line_act : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (ψ : AddChar (AF D.host.F) ℂ) (χ : AddChar k Circle), p.IsChar ψ χ →
    ∃ ε : k, (ε = 1 ∨ ε = -1) ∧ ∀ (n n' n'' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] [Fintype n''] [DecidableEq n''] (σ : ℕ) (B : BesLev D (σ + 1)) (B' : BesLev D σ) (W₀ : HSp D) (l : Link B B'.L B'.ζ) (α : Frame p B.A n') (α₀ : Frame p B.V₀ (n' ⊕ Fin 1)) (β : Frame p W₀ n) (γ : Frame p B'.A n'') (γ₀ : Frame p B'.V₀ (n'' ⊕ Fin 1)), IsSumFrame B.o B.ζ α α₀ → IsSumFrame B'.o B'.ζ γ γ₀ → IsStdChar D ψ (-1) → ∀ t : n → k,
      (∃ w₀ : WO W₀ B'.L,
        (∀ (L₁ : Lat B.V₀) (L₂ : Lat W₀) (f₁ : WO B.V₀ W₀ → ℂ) (Ψ₁ : Matrix n n' k → ℂ) (a : (n → k) → ℂ) (Ξ : WO B.V₀ W₀ → ℂ),
          Over ψ α₀ β L₁ L₂ f₁ (tensCol Ψ₁ a) Ξ →
          Over ψ α₀ β L₁ L₂ f₁ (tensCol Ψ₁ fun y => (χ (ε * (t ⬝ᵥ y)) : ℂ) * a y) (heisO ψ B.V₀ W₀ ((B.o.resS W₀).symm (0, l.κ W₀ w₀)) Ξ)) ∧
        (∀ (L₂' : Lat W₀) (L₃ : Lat B'.V₀) (f₂ : WO W₀ B'.V₀ → ℂ) (Ψ₂ : Matrix n'' n k → ℂ) (b : (n → k) → ℂ) (Ξ : WO W₀ B'.V₀ → ℂ),
          Over ψ β γ₀ L₂' L₃ f₂ (tensRow Ψ₂ b) Ξ →
          Over ψ β γ₀ L₂' L₃ f₂ (tensRow Ψ₂ fun η => b (η - t)) (heisO ψ W₀ B'.V₀ ((B'.o.resT W₀).symm (0, -w₀)) Ξ))) ∧
      (∃ w₀ : WO W₀ B'.L,
        (∀ (L₁ : Lat B.V₀) (L₂ : Lat W₀) (f₁ : WO B.V₀ W₀ → ℂ) (Ψ₁ : Matrix n n' k → ℂ) (a : (n → k) → ℂ) (Ξ : WO B.V₀ W₀ → ℂ),
          Over ψ α₀ β L₁ L₂ f₁ (tensCol Ψ₁ a) Ξ →
          Over ψ α₀ β L₁ L₂ f₁ (tensCol Ψ₁ fun y => a (y - t)) (heisO ψ B.V₀ W₀ ((B.o.resS W₀).symm (0, l.κ W₀ w₀)) Ξ)) ∧
        (∀ (L₂' : Lat W₀) (L₃ : Lat B'.V₀) (f₂ : WO W₀ B'.V₀ → ℂ) (Ψ₂ : Matrix n'' n k → ℂ) (b : (n → k) → ℂ) (Ξ : WO W₀ B'.V₀ → ℂ),
          Over ψ β γ₀ L₂' L₃ f₂ (tensRow Ψ₂ b) Ξ →
          Over ψ β γ₀ L₂' L₃ f₂ (tensRow Ψ₂ fun η => (χ (ε * (η ⬝ᵥ t)) : ℂ) * b η) (heisO ψ W₀ B'.V₀ ((B'.o.resT W₀).symm (0, -w₀)) Ξ))) := by
  intro D k _ _ _ _ p ψ χ hχ
  refine ⟨-1, Or.inr rfl, ?_⟩
  intro n n' n'' _ _ _ _ _ _ σ B B' W₀ l α α₀ β γ γ₀ hα hγ hstd t
  have hχc := (GlobalTheory.T.splitPlace_stdChar_continuous_nontrivial D k p ψ χ hχ hstd).1
  have hχl := GlobalTheory.RootEx.OpenKernel.isLocallyConstant_coe_addChar χ hχc
  have hlc : IsLocallyConstant fun y : n → k => (χ (-1 * (t ⬝ᵥ y)) : ℂ) :=
    hχl.comp_continuous (continuous_const.mul (continuous_const.dotProduct continuous_id))
  have hlc' : IsLocallyConstant fun η : n → k => (χ (-1 * (η ⬝ᵥ t)) : ℂ) :=
    hχl.comp_continuous (continuous_const.mul (continuous_id.dotProduct continuous_const))
  constructor
  · obtain ⟨h1h, h1m⟩ := GlobalTheory.T.kappa_splitHalfPoint_multiplies_by_character D k p ψ χ hχ n n' (σ + 1) B B'.L W₀ B'.ζ l α α₀ β hα t
    obtain ⟨h1ah, h1ar⟩ := GlobalTheory.T.neg_halfPoint_translates_lastFrameRow D k p n n'' B'.V₀ B'.A B'.L W₀ B'.o B'.ζ β γ γ₀ hγ t
    refine ⟨wRow p B'.ζ β t, fun L₁ L₂ f₁ Ψ₁ a Ξ h => ?_, fun L₂' L₃ f₂ Ψ₂ b Ξ h => ?_⟩
    · refine over_modul h h1h (tensCol_mul_mem hlc h.2.2.2.1) fun x hx => ?_
      rw [h1m x hx]
      simp only [tensCol, neg_one_mul]
      ring
    · refine over_trans h h1ah (tensRow_sub_mem t h.2.2.2.1) fun x hx => ?_
      simp only [tensRow, GlobalTheory.FinPl.OverProof.rd_add]
      congr 1
      · congr 1; ext i j; simp [Matrix.add_apply, h1ar]
      · congr 1; funext j; simp [Matrix.add_apply, h1ar, sub_eq_add_neg]
  · obtain ⟨h2h, h2r⟩ := GlobalTheory.T.kappa_conjugateHalfPoint_translates_lastColumn D k p n n' (σ + 1) B B'.L W₀ B'.ζ l B'.line α α₀ β hα t
    obtain ⟨h2bh, h2bm⟩ := GlobalTheory.T.conjugateHalfPoint_neg_multiplies_by_character D k p ψ χ hχ n n'' B'.V₀ B'.A B'.L W₀ B'.o B'.ζ B'.line β γ γ₀ hγ t
    refine ⟨wCol p B'.ζ β t, fun L₁ L₂ f₁ Ψ₁ a Ξ h => ?_, fun L₂' L₃ f₂ Ψ₂ b Ξ h => ?_⟩
    · refine over_trans h h2h (tensCol_sub_mem t h.2.2.2.1) fun x hx => ?_
      simp only [tensCol, GlobalTheory.FinPl.OverProof.rd_add]
      congr 1
      · congr 1; ext i j; simp [Matrix.add_apply, h2r]
      · congr 1; funext i; simp [Matrix.add_apply, h2r, sub_eq_add_neg]
    · refine over_modul h h2bh (tensRow_mul_mem hlc' h.2.2.2.1) fun x hx => ?_
      rw [h2bm x hx]
      simp only [tensRow, neg_one_mul]
      ring
end GlobalTheory.FinPl.LineAct
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.RootEx GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.SplitWeil GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FinPl.SplitParts

theorem mem_latV_iff_parts : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k) (S : HSp D) (L : GlobalTheory.FinPl.Lat S) (y : Fin S.rank → AE D), (∀ r, y r ∈ GlobalTheory.FinPl.idAt D (· = q.v)) → (y ∈ GlobalTheory.FinPl.latV S L (· = q.v) ↔ (fun r => q.e * y r) ∈ GlobalTheory.FinPl.latV S L (· = q.v) ∧ (fun r => cA D q.e * y r) ∈ GlobalTheory.FinPl.latV S L (· = q.v)) := by
  intro D k _ _ _ _ q S L y hy
  have he : finPart D q.e ∈ intAE D := GlobalTheory.UpMem.finPart_e_int q
  have hce : finPart D (cA D q.e) ∈ intAE D := (GlobalTheory.FinPl.FrameLat.cA_int_iff q.e).2 he
  constructor
  · intro h
    exact ⟨GlobalTheory.FinPl.LatIndHalf.mul_mem_latV he h, GlobalTheory.FinPl.LatIndHalf.mul_mem_latV hce h⟩
  · rintro ⟨h1, h2⟩
    have e : y = (fun r => q.e * y r) + (fun r => cA D q.e * y r) := by
      funext r
      rw [Pi.add_apply, ← add_mul, (GlobalTheory.FinPl.FrameLat.idem_iff q (y r)).1 (hy r)]
    rw [e]
    exact add_mem h1 h2

end GlobalTheory.FinPl.SplitParts
end
end
